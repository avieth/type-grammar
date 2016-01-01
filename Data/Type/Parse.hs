{-|
Module      : Data.Type.Parse
Description : Type parsing.
Copyright   : (c) Alexander Vieth, 2015
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Type.Parse where

import Data.Kind
import Data.Proxy
import qualified GHC.TypeLits as TypeLits (Nat, Symbol)

-- | The idea: just as the typical haskell function s -> t maps values of
--   type s to values of type t, we can define the type-level function
--   k ~> l which maps types of kind k to types of kind l.
--
--   Rolling our own term-function construction, we'd do something like this:
--
--     data Function (domain :: Type) (range :: Type) :: Type where
--         Function :: (domain -> range) -> Function domain range
--
--     runFunction :: Function domain range -> domain -> range
--     runFunction (Function f) = f
--
--   We of course must defer to the built-in notion of function (->). Doing
--   the same thing up here, with types and kinds, defers to the built-in
--   notion of type-function, the type family! But since we can't just embed
--   a type family into the GADT constructor as we did above, we take a type
--   called @functionDef@ assuming that it has appropriate type families defined
--   on it. Check out @TyFunctionClause@, which is analagous to pattern
--   matching on a particular kind.
--
data TyFunction (domain :: Type) (range :: Type) :: Type where
    TyFunction :: functionDef -> Proxy domain -> Proxy range -> TyFunction domain range

-- | Functions are actually implemented by this class. For each functionDef,
--   domain, and range pair, we have 0 or more clauses mapping a type of domain
--   to a type of range. This is like pattern matching on the domain kind.
type family TyFunctionClause (functionDef :: Type) domain range (x :: domain) :: range

-- | Function application can be performed without giving an explicit domain
--   and range kind; those are determined by the function type given as the
--   first parameter.
type family RunTyFunction (f :: TyFunction domain range) (x :: domain) :: range where
    RunTyFunction ('TyFunction functionDef ('Proxy :: Proxy domain) ('Proxy :: Proxy range)) x =
        TyFunctionClause functionDef domain range x

-- |
-- = Input stream handling
--
-- To make term parsers bounded-polymorphic in their inputs, an author might
-- choose a typeclass like this
--
--   @
--     class Stream s where
--         type Character s :: *
--         splitStream :: s -> Maybe (Character s, s)
--   @
--
-- which describes how to pull the head of the stream, and give back the
-- remainder.
-- We do something similar here, using a type family. The first parameter
-- is the kind of stream element, and the second is the type of the stream
-- itself. Two instances are given.
-- The instance for (Type -> Type) (input :: Type) describes how to handle a
-- sequence of type constructors, like Maybe [Maybe EOF].
type family InputSplit k (input :: inputKind) :: Maybe (k, inputKind)

type instance InputSplit (Type -> Type) (ty :: Type) = InputSplitTypeStream ty
type family InputSplitTypeStream (ty :: Type) :: Maybe (Type -> Type, Type) where
    InputSplitTypeStream (ty rest) = 'Just '(ty, rest)
    InputSplitTypeStream anythingElse = 'Nothing

type instance InputSplit k (l :: [k]) = InputSplitList l
type family InputSplitList (l :: [k]) :: Maybe (k, [k]) where
    InputSplitList '[] = 'Nothing
    InputSplitList (x ': xs) = 'Just '(x, xs)

-- |
-- = Parsing
--
-- The following definitions give type-level parsing. It's probably good to
-- keep up an analogy with term-level parsers, as what we do is exactly that,
-- but with terms replaced by types and types replaced by kinds.
--
-- We mirror the simple pure-functional parser given by this type:
--
--     @
--       newtype Parser stream t = Parser {
--             runParser :: stream -> Maybe (t, stream)
--           }
--     @
--
-- Instead of a type @Parser stream t@, we give a *kind* @Parser stream t@
-- inhabited by various types of parsers, like fmap, applicative pure and
-- <*>, monadic join, etc.
-- Whereas @runParser@ is a function on terms, we give @RunParser@, a function
-- on types (a type family).

-- | The result of a parse. It's analagous to Maybe (t, stream) from a canonical
--   pure functional term parser.
data Result output remainder where
    NoParse :: Result output remainder
    Parsed :: output -> remainder -> Result output remainder

-- | The parser kind.
--
--   Some parsers must be explicitly kinded. Pure, Empty, Match in particular.
--   For the higher-order parsers, the kind can be inferred from the parts.
--
data Parser (input :: Type) (output :: Type) :: Type where
    Pure :: Proxy inputKind -> outputKind -> Parser inputKind outputKind
    Empty :: Proxy inputKind -> Proxy outputKind -> Parser inputKind outputKind
    Match :: Proxy inputKind -> match -> Parser inputKind match
    Fmap :: (k -> l) -> Parser inputKind k -> Parser inputKind l
    Ap :: Parser inputKind (k -> l) -> Parser inputKind k -> Parser inputKind l
    Alt :: Parser inputKind outputKind -> Parser inputKind outputKind -> Parser inputKind outputKind
    Join :: Parser inputKind (Parser inputKind outputKind) -> Parser inputKind outputKind
    -- Here's an asymmetry with the term parser case.
    -- Using Fmap we can lift data constructors through parsers.
    -- But what about type families? Those are weird animals, which cannot be
    -- curried nor partially applied. To handle them, we offer one parser
    -- type which applies a single-argument type family (no currying, use
    -- tuples or similar). The arguments can be gathered using Fmap and Ap,
    -- then applied using this constructor.
    ApplyTyFunction :: TyFunction k l -> Parser inputKind k -> Parser inputKind l
    -- Recursive parsers naturally lead to infinite types. To make recursive
    -- parsers viable, we use explicit laziness. A new type, @thunk@, is
    -- used to stand in for the suspended parser. It must have the type family
    -- Force defined on it.
    Suspend :: thunk -> Proxy inputKind -> Proxy outputKind -> Parser inputKind outputKind

type family RunParser (parser :: Parser inputKind outputKind) (input :: inputKind) :: Result outputKind inputKind where

    RunParser ('Pure 'Proxy x) input = 'Parsed x input

    RunParser ('Empty 'Proxy outputKind) input = 'NoParse

    RunParser ('Match 'Proxy (match :: k)) input =
        RunParserMatch match (InputSplit k input)

    RunParser ('Fmap f parser) input =
        RunParserFmap f (RunParser parser input)

    RunParser ('Ap parserF parserX) input =
        RunParserAp parserF parserX input

    RunParser ('Alt parserLeft parserRight) input =
        RunParserAlt parserLeft parserRight input

    RunParser ('Join parser) input = RunParserJoin (RunParser parser input)

    RunParser ('ApplyTyFunction f parser) input =
        RunParserApplyTyFunction f (RunParser parser input)

    RunParser ('Suspend thunk ('Proxy :: Proxy inputKind) ('Proxy :: Proxy outputKind)) input =
        RunParser (Force thunk inputKind outputKind) input

type family RunParserMatch (match :: k) (split :: Maybe (k, inputKind)) :: Result k inputKind where
    RunParserMatch match 'Nothing = 'NoParse
    RunParserMatch match ('Just '(match, remaining)) = 'Parsed match remaining
    RunParserMatch match ('Just '(anythingElse, remaining)) = 'NoParse

type family RunParserFmap (f :: k -> l) (result :: Result k inputKind) :: Result l inputKind where
    RunParserFmap f 'NoParse = 'NoParse
    RunParserFmap f ('Parsed (output :: k) remainder) =
        'Parsed (f output) remainder

type family RunParserAp (parserF :: Parser inputKind (k -> l)) (parserX :: Parser inputKind k) (input :: inputKind) :: Result l inputKind where
    RunParserAp parserF parserX input = RunParserApLeft (RunParser parserF input) parserX

type family RunParserApLeft (resultF :: Result (k -> l) inputKind) (parserX :: Parser inputKind k) :: Result l inputKind where
    RunParserApLeft 'NoParse parserX = 'NoParse
    RunParserApLeft ('Parsed f remaining) parserX = RunParserApRight f (RunParser parserX remaining)

type family RunParserApRight (f :: k -> l) (resultX :: Result k inputKind) :: Result l inputKind where
    RunParserApRight f 'NoParse = 'NoParse
    RunParserApRight f ('Parsed x remaining) = 'Parsed (f x) remaining

type family RunParserAlt (parserLeft :: Parser inputKind k) (parserRight :: Parser inputKind k) (input :: inputKind) :: Result k inputKind where
    RunParserAlt parserLeft parserRight input = RunParserAltLeft (RunParser parserLeft input) parserRight input

type family RunParserAltLeft (resultLeft :: Result k inputKind) (parserRight :: Parser inputKind k) (input :: inputKind) :: Result k inputKind where
    RunParserAltLeft 'NoParse parserRight input = RunParser parserRight input
    RunParserAltLeft ('Parsed x remaining) parserRight input = 'Parsed x remaining

type family RunParserJoin (result :: Result (Parser inputKind k) inputKind) :: Result k inputKind where
    RunParserJoin 'NoParse = 'NoParse
    RunParserJoin ('Parsed parser remainder) = RunParser parser remainder

type family RunParserApplyTyFunction (f :: TyFunction k l) (result :: Result k inputKind) :: Result l inputKind where
    RunParserApplyTyFunction f 'NoParse = 'NoParse
    RunParserApplyTyFunction f ('Parsed x remaining) = 'Parsed (RunTyFunction f x) remaining

type family Force (thunk :: t) inputKind outputKind :: Parser inputKind outputKind

type (:<$>) = Fmap
type (:<*>) = Ap
type (:<|>) = Alt

type TyFst = 'TyFunction TyFstDef ('Proxy :: Proxy (k, l)) ('Proxy :: Proxy k)
data TyFstDef
type instance TyFunctionClause TyFstDef (k, l) k '(x, y) = x

type TySnd = 'TyFunction TySndDef ('Proxy :: Proxy (k, l)) ('Proxy :: Proxy l)
data TySndDef
type instance TyFunctionClause TySndDef (k, l) l '(x, y) = y

type x :<* y = 'ApplyTyFunction TyFst ( '(,) :<$> x :<*> y )
type x :*> y = 'ApplyTyFunction TySnd ( '(,) :<$> x :<*> y )

-- | To give an analogue for >>=, we might naively try
--
--     @type x :>>= y = 'Join (y :<$> x)@
--
--   but in order for this to be of any use, we must have @y :: k -> Parser i l@.
--   That's a bit too restrictive; we'd rather have @y@ represent some type
--   family with codomain @Parser i l@. So in fact we want
--
--     type x :>>= y = 'Join ('ApplyTyFunction y x)
--
--   So the kind of :>>= is in fact
--
--     @Parser inputKind k -> TyFunction k (Parser inputKind l) -> Parser inputKind l@
--
type x :>>= y = 'Join ('ApplyTyFunction y x)

type Ex1 = 'Pure ('Proxy :: Proxy Type) 'True

type TyNot = 'TyFunction TyNotDef ('Proxy :: Proxy Bool) ('Proxy :: Proxy Bool)
data TyNotDef
type instance TyFunctionClause TyNotDef Bool Bool 'True = 'False
type instance TyFunctionClause TyNotDef Bool Bool 'False = 'True

type Ex2 = 'ApplyTyFunction TyNot Ex1

-- Tuple the outputs of Ex1 and Ex2.
type Ex3 = 'Ap ('Fmap '(,) Ex1) Ex2

type TyAnd = 'TyFunction TyAndDef ('Proxy :: Proxy (Bool, Bool)) ('Proxy :: Proxy Bool)
data TyAndDef
type instance TyFunctionClause TyAndDef (Bool, Bool) Bool '(a, b) = BoolAnd a b

type family BoolAnd (a :: Bool) (b :: Bool) :: Bool where
    BoolAnd 'True 'True = 'True
    BoolAnd a b = 'False

type Ex4 = 'ApplyTyFunction TyAnd Ex3

-- | Use this to mark the EOF.
data EOF = EOF

-- | Show that a given type can be used to construct a value of some other
--   type.
--   TODO better name. This doesn't necessarily mean we have a singleton type.
class Singleton (t :: k) where
    type SingletonType t :: Type
    singleton :: Proxy t -> SingletonType t

instance Singleton output => Singleton ('Parsed output remainder) where
    type SingletonType ('Parsed output remainder) = SingletonType output
    singleton _ = singleton (Proxy :: Proxy output)

-- | For the @Many@ parser, we require a @List@ kind.
data List (t :: k) where
    Nil :: Proxy t -> List t
    Cons :: t -> List t -> List t

instance Singleton ('Nil ('Proxy :: Proxy t)) where
    type SingletonType ('Nil ('Proxy :: Proxy t)) = List t
    singleton _ = Nil Proxy

instance
    ( Singleton t
    , Singleton list
    , SingletonType list ~ List (SingletonType t)
    ) => Singleton ('Cons t list)
  where
    type SingletonType ('Cons t list) = List (SingletonType t)
    singleton _ = Cons (singleton (Proxy :: Proxy t)) (singleton (Proxy :: Proxy list))

-- | 0 or more occurrences of a parser.
type Many (parser :: Parser inputKind outputKind) =
    'Suspend (ManyThunk parser) ('Proxy :: Proxy inputKind) ('Proxy :: Proxy (List outputKind))
data ManyThunk (parser :: Parser inputKind outputKind)
type instance Force (ManyThunk (parser :: Parser inputKind outputKind)) inputKind (List outputKind) =
    ('Cons :<$> parser :<*> 'Suspend (ManyThunk parser) 'Proxy 'Proxy) :<|> 'Pure ('Proxy) ('Nil 'Proxy)

-- For the Many1 parser, we shall require a nonempty list.
data NonEmptyList (t :: k) where
    NonEmptyList :: t -> List t -> NonEmptyList t

instance
    ( Singleton t
    , Singleton list
    , SingletonType list ~ List (SingletonType t)
    ) => Singleton ('NonEmptyList t list)
  where
    type SingletonType ('NonEmptyList t list) = NonEmptyList (SingletonType t)
    singleton _ = NonEmptyList (singleton (Proxy :: Proxy t)) (singleton (Proxy :: Proxy list))

-- | At least 1 occurrence of a parser.
type Many1 (parser :: Parser inputKind outputKind) =
    'NonEmptyList :<$> parser :<*> Many parser

-- | 1 or more occurrences of @parser@, interspersed by @separator@.
type SepBy (parser :: Parser inputKind outputKind) (separator :: Parser inputKind separatorKind) =
    'NonEmptyList :<$> parser :<*> Many (separator :*> parser)
