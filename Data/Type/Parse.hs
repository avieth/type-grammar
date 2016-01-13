{-|
Module      : Data.Type.Parse
Description : Type parsing.
Copyright   : (c) Alexander Vieth, 2015
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)

Pure functional applicative/monadic parsing, but at the type level.
Your parsers parse types from types. They run at compile time.

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
import Data.Type.Function
import GHC.TypeLits -- (Character, Symbol, SplitSymbol, ConsSymbol, ToUpper, ToLower, IsSpace)

{-
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
--   notion of type-function, the type family!
--
--   Naively, we could try the very same thing, but it's no good because
--   type families can only be given fully saturated! So even though the
--   kind of our type family may be domain -> range, we cannot use it to
--   obtain a *type* of that kind, and therefore cannot embed it into a
--   type like 'Function above.
--
--   As a workaround, we use a
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
-}

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
-- itself.
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

type instance InputSplit Character (s :: Symbol) = SplitSymbol s

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

--type TyResultValue = 'TyFunction TyResultValueDef ('Proxy :: Proxy (Result output remainder)) ('Proxy :: Proxy output)
--data TyResultValueDef
--type instance TyFunctionClause TyResultValueDef (Result output remainder) output ('Parsed x r) = x

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

infixl 4 :<$>
type (:<$>) = 'Fmap

-- (<$) :: (a -> b) -> f c -> f (a -> b)
--
infixl 4 :<$
type f :<$ p = Pure 'Proxy f :<* p

type Pure (inputKindProxy :: Proxy inputKind) (x :: outputKind) =
    F (Fst 'Proxy 'Proxy) :<$> (C ('(,) x) :<$> 'Trivial inputKindProxy)

type EOF (inputKindProxy :: Proxy inputKind) (outputKindProxy :: Proxy outputKind) =
    'Negate ('Token inputKindProxy outputKindProxy)

infixl 4 :<*>
type (:<*>) = 'Ap

infixl 4 :<*
type x :<* y = F (Fst 'Proxy 'Proxy) :<$> (C '(,) :<$> x :<*> y)

infixl 4 :*>
type x :*> y = F (Snd 'Proxy 'Proxy) :<$> (C '(,) :<$> x :<*> y)

infixl 3 :<|>
type (:<|>) = 'Alt

infixl 1 :>>=
type x :>>= y = 'Join (y :<$> x)

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

data ListLength (l :: List t)
type instance FunctionCodomain ListLength = Nat
type instance EvalFunction (ListLength ('Nil 'Proxy)) = 0
type instance EvalFunction (ListLength ('Cons x rest)) = 1 + EvalFunction (ListLength rest)

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
    ((C 'Cons) :<$> parser :<*> 'Suspend (ManyThunk parser) 'Proxy 'Proxy) :<|> Pure ('Proxy) ('Nil 'Proxy)

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
    (C 'NonEmptyList) :<$> parser :<*> Many parser

-- | 1 or more occurrences of @parser@, interspersed by @separator@.
type SepBy (parser :: Parser inputKind outputKind) (separator :: Parser inputKind separatorKind) =
    (C 'NonEmptyList) :<$> parser :<*> Many (separator :*> parser)

type Optional (parser :: Parser inputKind outputKind) =
    ((C 'Just) :<$> parser) :<|> Pure 'Proxy 'Nothing

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
    (characterization :<$> parser) :>>= (F (MaybeParse ('Proxy :: Proxy inputKind) ('Proxy :: Proxy l)))

data MaybeParse (inputKindProxy :: Proxy inputKind) (outputKindProxy :: Proxy outputKind) x
type instance FunctionCodomain (MaybeParse ('Proxy :: Proxy inputKind) ('Proxy :: Proxy outputKind)) =
    Parser inputKind outputKind
type instance EvalFunction (MaybeParse 'Proxy 'Proxy 'Nothing) = 'Empty 'Proxy 'Proxy
type instance EvalFunction (MaybeParse 'Proxy 'Proxy ('Just x)) = Pure 'Proxy x

-- | A special case of match, in which the characterization is on a token.
--   You still have to indicate the kind of the input stream, but you can
--   probably get away without an annotation on the 'Proxy.
type MatchToken (characterization :: Characterization k l) (inputStreamProxy :: Proxy inputStream) =
    Match characterization ('Token inputStreamProxy ('Proxy :: Proxy k))

--type Satisfy (indicator :: TyFunction k Bool) = 

-- | An exact-match characterization. The input type must be the same as
--   the argument type @token@.
data Exact (token :: tokenKind) (challenge :: tokenKind)
type instance FunctionCodomain (Exact (token :: tokenKind)) = Maybe tokenKind
type instance EvalFunction (Exact token challenge) = EvalFunctionExact token challenge
type family EvalFunctionExact (token :: k) (challenge :: k) :: Maybe k where
    EvalFunctionExact token token = 'Just token
    EvalFunctionExact token token' = 'Nothing

type AnyChar = 'Token 'Proxy ('Proxy :: Proxy Character)

type ExactChar (c :: Character) = MatchToken (F (Exact c)) 'Proxy
type ExactCharCI (c :: Character) = ExactChar (ToUpper c) :<|> ExactChar (ToLower c)

type family ExactString (s :: Symbol) :: Parser Symbol Symbol where
    ExactString s = ExactString' (SplitSymbol s)
type family ExactString' (s :: Maybe (Character, Symbol)) :: Parser Symbol Symbol where
    ExactString' 'Nothing = Pure 'Proxy ""
    ExactString' ('Just '(c, rest)) = F ExactStringCons :<$> ExactChar c :<*> ExactString rest
type family ExactStringCI (s :: Symbol) :: Parser Symbol Symbol where
    ExactStringCI s = ExactStringCI' (SplitSymbol s)
type family ExactStringCI' (s :: Maybe (Character, Symbol)) :: Parser Symbol Symbol where
    ExactStringCI' 'Nothing = Pure 'Proxy ""
    ExactStringCI' ('Just '(c, rest)) = F ExactStringCons :<$> ExactCharCI c :<*> ExactStringCI rest
data ExactStringCons (c :: Character) (s :: Symbol)
type instance FunctionCodomain ExactStringCons = Symbol
type instance EvalFunction (ExactStringCons c s) = ConsSymbol c s

-- A characterization must produce a Maybe, but sometimes we want to use
-- boolean-valued functions to characterize. Thus we would like to take
-- a function  s -> Bool  and produce a function  s -> Maybe s.
-- Term-level, we would write
--
--   mkCharacterization f = \x -> if f x then Just x else Nothing
--
-- type-level, I suppose we'd need a new datatype.
-- TBD throw on the x paramter? Yeah, no explicit currying.
data BooleanCharacterization (p :: Proxy k) (f :: TyFunction k Bool) (x :: k)
type instance FunctionCodomain (BooleanCharacterization (p :: Proxy k) (f :: TyFunction k Bool)) = Maybe k
type instance EvalFunction (BooleanCharacterization (p :: Proxy k) (f :: TyFunction k Bool) x) = EvalBooleanCharacterization (f `At` x) x
type family EvalBooleanCharacterization (answer :: Bool) (x :: k) :: Maybe k where
    EvalBooleanCharacterization 'True x = 'Just x
    EvalBooleanCharacterization 'False x = 'Nothing

data IsSpaceDef (c :: Character)
type instance FunctionCodomain IsSpaceDef = Bool
type instance EvalFunction (IsSpaceDef c) = IsSpace c
type Whitespace = MatchToken (F (BooleanCharacterization ('Proxy :: Proxy Character) (F IsSpaceDef))) ('Proxy :: Proxy Symbol)

data ListToString (l :: List Character)
type instance FunctionCodomain ListToString = Symbol
type instance EvalFunction (ListToString ('Nil 'Proxy)) = ""
type instance EvalFunction (ListToString ('Cons c rest)) = ConsSymbol c (EvalFunction (ListToString rest))

data NonEmptyListToString (l :: NonEmptyList Character)
type instance FunctionCodomain NonEmptyListToString = Symbol
type instance EvalFunction (NonEmptyListToString ('NonEmptyList c list)) = ConsSymbol c (EvalFunction (ListToString list))

-- Expression parsing (infix operators).

data Operator inputKind outputKind where
    Infix  :: [Parser inputKind outputKind] -> Operator inputKind outputKind
    Infixl :: [Parser inputKind outputKind] -> Operator inputKind outputKind
    Infixr :: [Parser inputKind outputKind] -> Operator inputKind outputKind

data Expr base op where
    ExprOp :: Expr base op -> op -> Expr base op -> Expr base op
    ExprBase :: base -> Expr base op

data ExprRightAssoc (proxyBase :: Proxy base) (proxyOp :: Proxy op) (left :: Expr base op) (rights :: List (op, Expr base op))
type instance FunctionCodomain (ExprRightAssoc ('Proxy :: Proxy base) ('Proxy :: Proxy op)) = Expr base op
type instance EvalFunction (ExprRightAssoc base op left rights) = MkExprRightAssoc left rights

data ExprLeftAssoc (proxyBase :: Proxy base) (proxyOp :: Proxy op) (lefts :: List (Expr base op, op)) (right :: Expr base op)
type instance FunctionCodomain (ExprLeftAssoc ('Proxy :: Proxy base) ('Proxy :: Proxy op)) = Expr base op
type instance EvalFunction (ExprLeftAssoc base op lefts right) = MkExprLeftAssoc lefts right

type family MkExprRightAssoc (left :: Expr base op) (list :: List (op, Expr base op)) :: Expr base op where
    MkExprRightAssoc left ('Nil 'Proxy) = left
    MkExprRightAssoc left ('Cons '(op, right) rest) =
        'ExprOp left op (MkExprRightAssoc right rest)

type family MkExprLeftAssoc (list :: List (Expr base op, op)) (right :: Expr base op) :: Expr base op where
    MkExprLeftAssoc left right =
        MkExprLeftAssocShifted (LeftmostLeftAssoc left right) (ShiftLeftAssoc left right)

type family MkExprLeftAssocShifted (left :: Expr base op) (list :: List (op, Expr base op)) :: Expr base op where
    MkExprLeftAssocShifted left ('Nil 'Proxy) = left
    MkExprLeftAssocShifted left ('Cons '(op, right) rest) =
        MkExprLeftAssocShifted ('ExprOp left op right) rest

type family LeftmostLeftAssoc (list :: List (Expr base op, op)) (right :: Expr base op) :: Expr base op where
    LeftmostLeftAssoc ('Nil 'Proxy) right = right
    LeftmostLeftAssoc ('Cons '(expr, op) rest) right = expr

-- Left-shift the list.
type family ShiftLeftAssoc (list :: List (Expr base op, op)) (right :: Expr base op) :: List (op, Expr base op) where
    ShiftLeftAssoc ('Nil 'Proxy) right = 'Nil 'Proxy
    ShiftLeftAssoc ('Cons '(expr, op) ('Nil 'Proxy)) right =
        'Cons '(op, right) ('Nil 'Proxy)
    ShiftLeftAssoc ('Cons '(expr1, op1) ('Cons '(expr2, op2) rest)) right =
        'Cons '(op1, expr2) (ShiftLeftAssoc ('Cons '(expr2, op2) rest) right)

type family MkInfixrAlternatives (parseBase :: Parser inputKind base) (parsers :: [Parser inputKind op]) :: Parser inputKind (op, base) where
    MkInfixrAlternatives base '[] = 'Empty 'Proxy 'Proxy
    MkInfixrAlternatives base ( op ': rest ) =
        MkInfixrAlternatives base rest :<|> (C '(,) :<$> op :<*> base) 

type family MkInfixlAlternatives (parseBase :: Parser inputKind base) (parsers :: [Parser inputKind op]) :: Parser inputKind (base, op) where
    MkInfixlAlternatives base '[] = 'Empty 'Proxy 'Proxy
    MkInfixlAlternatives base ( op ': rest ) =
        (C '(,) :<$> base :<*> op) :<|> MkInfixlAlternatives base rest

data ParseExpr inputKind base op where
    ParseExpr
        -- The list of all operators, ascending precedence.
        :: [Operator inputKind op]
        -- A tail of the list of all operators. It's useful to keep it here so
        -- that a 'ParseExpr contains all of the information necessary to
        -- expand itself into a parser type (by recursing on the operator list).
        -> [Operator inputKind op]
        -> Parser inputKind base
        -> Parser inputKind ()
        -> Parser inputKind ()
        -> ParseExpr inputKind base op

type family MkParseExpr (ops :: [Operator inputKind op]) (baseParser :: Parser inputKind base) (lparen :: Parser inputKind ()) (rparen :: Parser inputKind ()) :: Parser inputKind (Expr base op) where
    MkParseExpr (ops :: [Operator inputKind op]) (parseBase :: Parser inputKind base) lparen rparen =
        'Suspend ('ParseExpr ops ops parseBase lparen rparen) ('Proxy :: Proxy inputKind) ('Proxy :: Proxy (Expr base op))

type instance Force ('ParseExpr (ops :: [Operator inputKind op]) (opsRec :: [Operator inputKind op]) (parseBase :: Parser inputKind base) lparen rparen) inputKind (Expr base op) =
    ParseExprExpand ('ParseExpr ops opsRec parseBase lparen rparen)

-- To make the expression parser we must always have in hand the
-- ParseExpr thunk, so that we can recurse. The family itself must recurse on
-- the operators list, so that comes as another parameter.
type family ParseExprExpand (pe :: ParseExpr inputKind base op)
                            :: Parser inputKind (Expr base op) where

    ParseExprExpand ('ParseExpr (ops :: [Operator inputKind op]) '[] (parseBase :: Parser inputKind base) lparen rparen) =
             (C 'ExprBase :<$> parseBase)
        :<|> (   lparen
             :*> 'Suspend ('ParseExpr ops ops parseBase lparen rparen) ('Proxy :: Proxy inputKind) ('Proxy :: Proxy (Expr base op))
             :<* rparen
             )

    ParseExprExpand ('ParseExpr (ops :: [Operator inputKind op]) ('Infix '[] ': opsrest) (parseBase :: Parser inputKind base) lparen rparen) =
        'Suspend ('ParseExpr ops opsrest parseBase lparen rparen) ('Proxy :: Proxy inputKind) ('Proxy :: Proxy (Expr base op))

    ParseExprExpand ('ParseExpr (ops :: [Operator inputKind op]) ('Infix ( inf ': infixrest ) ': opsrest) (parseBase :: Parser inputKind base) lparen rparen) =
             (    C 'ExprOp
             :<$> 'Suspend ('ParseExpr ops opsrest parseBase lparen rparen) ('Proxy :: Proxy inputKind) ('Proxy :: Proxy (Expr base op))
             :<*> inf
             :<*> 'Suspend ('ParseExpr ops opsrest parseBase lparen rparen) ('Proxy :: Proxy inputKind) ('Proxy :: Proxy (Expr base op))
             )
        :<|> 'Suspend ('ParseExpr ops ('Infix infixrest ': opsrest) parseBase lparen rparen) ('Proxy :: Proxy inputKind) ('Proxy :: Proxy (Expr base op))


    ParseExprExpand ('ParseExpr (ops :: [Operator inputKind op]) ('Infixl infixls ': opsrest) (parseBase :: Parser inputKind base) lparen rparen) =
             F (ExprLeftAssoc ('Proxy :: Proxy base) ('Proxy :: Proxy op))
        :<$> Many (MkInfixlAlternatives ('Suspend ('ParseExpr ops opsrest parseBase rparen lparen) ('Proxy :: Proxy inputKind) ('Proxy :: Proxy (Expr base op)))
                                        infixls
                  )
        :<*> 'Suspend ('ParseExpr ops opsrest parseBase rparen lparen) ('Proxy :: Proxy inputKind) ('Proxy :: Proxy (Expr base op))

    ParseExprExpand ('ParseExpr (ops :: [Operator inputKind op]) ('Infixr infixrs ': opsrest) (parseBase :: Parser inputKind base) lparen rparen) =
             F (ExprRightAssoc ('Proxy :: Proxy base) ('Proxy :: Proxy op))
        :<$> 'Suspend ('ParseExpr ops opsrest parseBase rparen lparen) ('Proxy :: Proxy inputKind) ('Proxy :: Proxy (Expr base op))
        :<*> Many (MkInfixrAlternatives ('Suspend ('ParseExpr ops opsrest parseBase rparen lparen) ('Proxy :: Proxy inputKind) ('Proxy :: Proxy (Expr base op)))
                                        infixrs
                  )

type Test1 = MkParseExpr ('[] :: [Operator Symbol Character])
                         (ExactChar 'a')
                         (ExactChar '(' :*> Pure 'Proxy '())
                         (ExactChar ')' :*> Pure 'Proxy '())
type Test2 = MkParseExpr ('[ 'Infixr '[ ExactChar '+' ] ])
                         (ExactChar 'a')
                         (ExactChar '(' :*> Pure 'Proxy '())
                         (ExactChar ')' :*> Pure 'Proxy '())
