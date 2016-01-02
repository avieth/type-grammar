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

type At f x = RunTyFunction f x

-- |
-- = Lifting type constructors to TyFunctions.
--
-- Type constructors (those things of kind k -> l) determine TyFunctions, but
-- it takes a little bit of work to lift them.
--
-- First, we make a family which computes the kind of the 'TyFunction which
-- they induce, which includes of course the domain and the range. For curried
-- type constructors like '(,) we get curried TyFunctions.
-- This kind is used as a parameter for the family @TyConstructors@, which
-- takes the actual type constructor and computes the 'TyFunction type
-- by way of TyConstructorDef, whose function clauses partially apply the
-- constructor until it's saturated.
--
--   @
--     :kind! TyCon '(,,) `At` Bool `At` Int `At` 'True
--     TyCon '(,,) `At` Bool `At` Int `At` 'True :: (*, *, Bool)
--     = '(Bool, Int, 'True)
--   @
--

type TyCon (c :: k) = TyConstructor (TyConstructorFunctionKind c) c

type family TyConstructorFunctionKind (c :: k) :: Type where
    TyConstructorFunctionKind (c :: k -> l) = TyConstructorFunctionKindExplicit k l
type family TyConstructorFunctionKindExplicit (domain :: Type) (range :: Type) :: Type where
    TyConstructorFunctionKindExplicit domain (range1 -> range2) =
        TyFunction domain (TyConstructorFunctionKindExplicit range1 range2)
    TyConstructorFunctionKindExplicit domain range = TyFunction domain range

type family TyConstructor (functionKind :: Type) (c :: k) :: functionKind where
    TyConstructor (TyFunction domain range) (c :: domain -> range') =
        'TyFunction (TyConstructorDef c) ('Proxy :: Proxy domain) ('Proxy :: Proxy range)

data TyConstructorDef (c :: k)
type instance TyFunctionClause (TyConstructorDef c) domain range x =
    TyFunctionClauseConstructorDef c domain range x

type family TyFunctionClauseConstructorDef (c :: k) (domain :: Type) (range :: Type) (x :: domain) :: range where
    TyFunctionClauseConstructorDef (c :: domain -> range) domain (TyFunction range1 range2) x =
        'TyFunction (TyConstructorDef (c x)) ('Proxy :: Proxy range1) ('Proxy :: Proxy range2)
    TyFunctionClauseConstructorDef (c :: domain -> range) domain range x = c x

type family TyConstructorAsTyFunction (c :: Type) :: Type where
    TyConstructorAsTyFunction (s -> (t -> u)) = TyFunction s (TyConstructorAsTyFunction (t -> u))
    TyConstructorAsTyFunction (s -> t) = TyFunction s t

-- (.) :: (t -> u) -> (s -> t) -> (s -> u)
-- This is a curried TyFunction. Observe how explicit we must be. Every
-- parameter must be gathered up in the Def types, so that they are still
-- around for use in the TyFunctionClause when we reach the end.
type TyCompose = 'TyFunction TyComposeDef
                             ('Proxy :: Proxy (TyFunction t u))
                             ('Proxy :: Proxy (TyFunction (TyFunction s t) (TyFunction s u)))
data TyComposeDef
type instance TyFunctionClause TyComposeDef (TyFunction t u) (TyFunction (TyFunction s t) (TyFunction s u)) g =
    'TyFunction (TyComposeDef1 g) ('Proxy :: Proxy (TyFunction s t)) ('Proxy :: Proxy (TyFunction s u))
data TyComposeDef1 (g :: TyFunction t u)
type instance TyFunctionClause (TyComposeDef1 (g :: TyFunction t u)) (TyFunction s t) (TyFunction s u) f =
    'TyFunction (TyComposeDef2 g f) ('Proxy :: Proxy s) ('Proxy :: Proxy u)
data TyComposeDef2 (g :: TyFunction t u) (f :: TyFunction s t)
type instance TyFunctionClause (TyComposeDef2 (g :: TyFunction t u) (f :: TyFunction s t)) s u x =
    g `At` (f `At` x)

infixr 9 :.
type g :. f = TyCompose `At` g `At` f

infixr 1 >>>
type f >>> g = g :. f

-- id :: t -> t as a type function.
type TyId = 'TyFunction TyIdDef ('Proxy :: Proxy k) ('Proxy :: Proxy k)
data TyIdDef
type instance TyFunctionClause TyIdDef k k x = x

-- const :: t -> s -> t as a type function. We treat it uncurried, so it's more
-- akin to uncurry const :: (t, s) -> t
type TyConst = 'TyFunction TyConstDef ('Proxy :: Proxy (k, l)) ('Proxy :: Proxy k)
data TyConstDef
type instance TyFunctionClause TyConstDef (k, l) k '(x, y) = x

-- fst :: (s, t) -> s as a type function. This is exactly the same as
-- uncurry const.
type TyFst = TyConst

-- swap :: (s, t) -> (t, s)
type TySwap = 'TyFunction TySwapDef ('Proxy :: Proxy (l, k)) ('Proxy :: Proxy (k, l))
data TySwapDef
type instance TyFunctionClause TySwapDef (l, k) (k, l) '(x, y) = '(y, x)

-- snd :: (s, t) -> t as a type function.
type TySnd = TyFst :. TySwap

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
-- sequence of type constructors, like Maybe [Maybe End].
type family InputSplit k (input :: inputKind) :: Maybe (k, inputKind)

type instance InputSplit (Type -> Type) (ty :: Type) = InputSplitTypeStream ty
type family InputSplitTypeStream (ty :: Type) :: Maybe (Type -> Type, Type) where
    InputSplitTypeStream (ty rest) = 'Just '(ty, rest)
    InputSplitTypeStream anythingElse = 'Nothing

-- | Use this to mark the EOF in a sequence of Type -> Type.
data End = End

type instance InputSplit k (l :: [k]) = InputSplitList l
type family InputSplitList (l :: [k]) :: Maybe (k, [k]) where
    InputSplitList '[] = 'Nothing
    InputSplitList (x ': xs) = 'Just '(x, xs)

-- |
-- = Parsing
--
-- The following definitions give type-level parsers. It's probably good to
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
-- inhabited by various types of parsers, like fmap, and monadic join.
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

    -- Always parses, without consuming input.
    Trivial :: Proxy inputKind -> Parser inputKind ()

    -- Never parses, never consumes input.
    -- NB this cannot be implemented in terms of Trivial and Negate, because
    -- 'Negate ('Trivial 'Proxy) :: Parser inputKind () but we need that
    -- output kind to be free, not ().
    Empty :: Proxy inputKind -> Proxy outputKind -> Parser inputKind outputKind

    -- Parses without consuming input iff the argument parser parses.
    Negate :: Parser inputKind outputKind -> Parser inputKind ()

    -- Take a token from the stream.
    Token :: Proxy inputKind -> Proxy outputKind -> Parser inputKind outputKind

    Fmap :: (TyFunction k l) -> Parser inputKind k -> Parser inputKind l
    Ap :: Parser inputKind (TyFunction k l) -> Parser inputKind k -> Parser inputKind l
    Alt :: Parser inputKind outputKind -> Parser inputKind outputKind -> Parser inputKind outputKind
    Join :: Parser inputKind (Parser inputKind outputKind) -> Parser inputKind outputKind

    -- Recursive parsers naturally lead to infinite types. To make recursive
    -- parsers viable, we use explicit laziness. A new type, @thunk@, is
    -- used to stand in for the suspended parser. It must have the type family
    -- Force defined on it.
    Suspend :: thunk -> Proxy inputKind -> Proxy outputKind -> Parser inputKind outputKind

type family RunParser (parser :: Parser inputKind outputKind) (input :: inputKind) :: Result outputKind inputKind where

    RunParser ('Trivial 'Proxy) input = 'Parsed '() input

    RunParser ('Empty 'Proxy 'Proxy) input = 'NoParse

    RunParser ('Negate parser) input = RunParserNegate (RunParser parser input) input

    RunParser ('Token ('Proxy :: Proxy inputKind) ('Proxy :: Proxy outputKind)) (input :: inputKind) =
        RunParserToken (InputSplit outputKind input)

    RunParser ('Fmap f parser) input =
        RunParserFmap f (RunParser parser input)

    RunParser ('Ap parserF parserX) input =
        RunParserAp parserF parserX input

    RunParser ('Alt parserLeft parserRight) input =
        RunParserAlt parserLeft parserRight input

    RunParser ('Join parser) input = RunParserJoin (RunParser parser input)

    RunParser ('Suspend thunk ('Proxy :: Proxy inputKind) ('Proxy :: Proxy outputKind)) input =
        RunParser (Force thunk inputKind outputKind) input

type family RunParserNegate (result :: Result outputKind inputKind) (input :: inputKind) :: Result () inputKind where
    RunParserNegate 'NoParse input = 'Parsed '() input
    RunParserNegate ('Parsed output remainder) input = 'NoParse

type family RunParserToken (split :: Maybe (outputKind, inputKind)) :: Result outputKind inputKind where
    RunParserToken 'Nothing = 'NoParse
    RunParserToken ('Just '(token, remaining)) = 'Parsed token remaining

type family RunParserFmap (f :: TyFunction k l) (result :: Result k inputKind) :: Result l inputKind where
    RunParserFmap f 'NoParse = 'NoParse
    RunParserFmap f ('Parsed (output :: k) remainder) =
        'Parsed (f `At` output) remainder

type family RunParserAp (parserF :: Parser inputKind (TyFunction k l)) (parserX :: Parser inputKind k) (input :: inputKind) :: Result l inputKind where
    RunParserAp parserF parserX input = RunParserApLeft (RunParser parserF input) parserX

type family RunParserApLeft (resultF :: Result (TyFunction k l) inputKind) (parserX :: Parser inputKind k) :: Result l inputKind where
    RunParserApLeft 'NoParse parserX = 'NoParse
    RunParserApLeft ('Parsed f remaining) parserX = RunParserApRight f (RunParser parserX remaining)

type family RunParserApRight (f :: TyFunction k l) (resultX :: Result k inputKind) :: Result l inputKind where
    RunParserApRight f 'NoParse = 'NoParse
    RunParserApRight f ('Parsed x remaining) = 'Parsed (f `At` x) remaining

type family RunParserAlt (parserLeft :: Parser inputKind k) (parserRight :: Parser inputKind k) (input :: inputKind) :: Result k inputKind where
    RunParserAlt parserLeft parserRight input = RunParserAltLeft (RunParser parserLeft input) parserRight input

type family RunParserAltLeft (resultLeft :: Result k inputKind) (parserRight :: Parser inputKind k) (input :: inputKind) :: Result k inputKind where
    RunParserAltLeft 'NoParse parserRight input = RunParser parserRight input
    RunParserAltLeft ('Parsed x remaining) parserRight input = 'Parsed x remaining

type family RunParserJoin (result :: Result (Parser inputKind k) inputKind) :: Result k inputKind where
    RunParserJoin 'NoParse = 'NoParse
    RunParserJoin ('Parsed parser remainder) = RunParser parser remainder

type family Force (thunk :: t) inputKind outputKind :: Parser inputKind outputKind

-- |
-- = Some derived parsers

type (:<$>) = Fmap

type Pure (inputKindProxy :: Proxy inputKind) (x :: outputKind) =
    TyConst :<$> ( (TyCon ('(,) x)) :<$> 'Trivial inputKindProxy)

type EOF (inputKindProxy :: Proxy inputKind) (outputKindProxy :: Proxy outputKind) =
    'Negate ('Token inputKindProxy outputKindProxy)

type (:<*>) = Ap
type (:<|>) = Alt

type x :<* y = TyFst :<$> (TyCon '(,) :<$> x :<*> y)
type x :*> y = TySnd :<$> (TyCon '(,) :<$> x :<*> y)

type x :>>= y = 'Join (y :<$> x)

-- To match on particular types, the programmar must characterize which
-- types will match, by giving a TyFunction with codomain Maybe k and
-- apply this to a parser using ApplyTyFunction. Now we have something that
-- looks like this
--
--     @Parser inputKind (Maybe k)@
--
-- By way of the TyMaybeParse function and Join, we can recover a
-- 
--     @Parser inputKind k@
--
-- which parses only when that Maybe is 'Just

type Characterization k l = TyFunction k (Maybe l)

type Match (characterization :: Characterization k l) (parser :: Parser inputKind k) =
    (characterization :<$> parser) :>>= TyMaybeParse l ('Proxy :: Proxy inputKind)

type TyMaybeParse k (inputKindProxy :: Proxy inputKind) =
    'TyFunction TyMaybeParseDef ('Proxy :: Proxy (Maybe k)) ('Proxy :: Proxy (Parser inputKind k))
data TyMaybeParseDef
type instance TyFunctionClause TyMaybeParseDef (Maybe k) (Parser inputKind k) 'Nothing = 'Empty 'Proxy 'Proxy
type instance TyFunctionClause TyMaybeParseDef (Maybe k) (Parser inputKind k) ('Just x) = Pure 'Proxy x

-- | A special case of match, in which the characterization is on a token.
--   You still have to indicate the kind of the input stream, but you can
--   probably get away without an annotation on the 'Proxy.
type MatchToken (characterization :: Characterization k l) (inputStreamProxy :: Proxy inputStream) =
    Match characterization ('Token inputStreamProxy ('Proxy :: Proxy k))

-- | An exact-match characterization. The input type must be the same as
--   the argument type @token@.
type Exact (token :: tokenKind) = 'TyFunction (ExactDef token) ('Proxy :: Proxy tokenKind) ('Proxy :: Proxy (Maybe tokenKind))
data ExactDef (token :: tokenKind)
type instance TyFunctionClause (ExactDef (token :: tokenKind)) tokenKind (Maybe tokenKind) input = TyFunctionClauseExact token input
type family TyFunctionClauseExact (token :: tokenKind) (input :: tokenKind) :: Maybe tokenKind where
    TyFunctionClauseExact token token = 'Just token
    TyFunctionClauseExact token anythingElse = 'Nothing

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
    ((TyCon 'Cons) :<$> parser :<*> 'Suspend (ManyThunk parser) 'Proxy 'Proxy) :<|> Pure ('Proxy) ('Nil 'Proxy)

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
    (TyCon 'NonEmptyList) :<$> parser :<*> Many parser

-- | 1 or more occurrences of @parser@, interspersed by @separator@.
type SepBy (parser :: Parser inputKind outputKind) (separator :: Parser inputKind separatorKind) =
    (TyCon 'NonEmptyList) :<$> parser :<*> Many (separator :*> parser)
