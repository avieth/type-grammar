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
{-# LANGUAGE UndecidableInstances #-}

module Data.Type.Parse where

import Data.Kind
import Data.Proxy
import qualified GHC.TypeLits as TypeLits (Nat, Symbol)

-- | The result of a parse. It's analagous to Maybe (t, stream) from a canonical
--   pure functional term parser.
data Result (output :: o) (input :: i) where
    NoParse :: Result output input
    Parsed :: output -> input -> Result output input

-- | Every parser must indicate the kind of its output by giving a clause for
--   this family.
type family ParseOutputKind ty :: Type

-- | The family Parse means that @ty@, the parser, will take a type @input@ of
--   kind @inputKind@, and give a @Result@ with the remaining input (has the
--   same kind as the input) and a type of the @outputKind@.
--
--   This is in direct analogy to the canonical term parser. Suppose we have
--   a parser type like this:
--
--     @
--       newtype Parser input outputType = Parser {
--             runParser :: input -> Maybe (outputType, input)
--           }
--     @
--
--   The type of @runParser@ is illustrative of the point:
--
--     @
--       runParser :: Parser input outputType -> input -> Maybe (outputType, input)
--     @
--
--   It's a function on values, but what would the same idea look like as a
--   function on types?
--
--     @
--       type family Parse (parser :: parserKind) (input :: inputKind) :: Maybe (?, inputKind)
--     @
--
--   We include @outputKind@ so we can fill in that question mark.
type family Parse (outputKind :: Type) ty (input :: inputKind) :: Result outputKind inputKind

-- | The empty parser never parses. This is like @empty@ from @Alternative@.
data Empty
type instance ParseOutputKind Empty = Type
type instance Parse outputKind Empty input = NoParse

-- | The trivial parser always parses, giving @t@ and consuming no input.
--   This is like @pure@.
data Trivial (t :: k)
type instance ParseOutputKind (Trivial (t :: k)) = k
type instance Parse k (Trivial (t :: k)) (input :: inputKind) = Parsed t input

-- | Match a particular type from a stream. If the head of the stream is
--   @character rest@ then it matches. Anything else and it does not.
data Match character

type instance ParseOutputKind (Match (character :: c)) = c
type instance Parse c (Match (character :: c)) (input :: inputKind) =
    ParseMatch character input

type family ParseMatch (character :: c) (input :: inputKind) :: Result c inputKind where
    ParseMatch character (character rest) = 'Parsed character rest
    ParseMatch character anythingElse = 'NoParse

-- | Match any @Sym sym@ (sym is a type-level string).
data AnySym

type instance ParseOutputKind AnySym = TypeLits.Symbol
type instance Parse TypeLits.Symbol AnySym input = ParseSymbol input

type family ParseSymbol (input :: inputKind) :: Result TypeLits.Symbol inputKind where
    ParseSymbol (Sym sym rest) = 'Parsed sym rest
    ParseSymbol anythingElse = 'NoParse

data Sym (sym :: TypeLits.Symbol) (t :: Type) where
    Sym :: Proxy sym -> t -> Sym sym t

-- | Match any @Nat nat@ (nat is a type-level natural number).
data AnyNat

type instance ParseOutputKind AnyNat = TypeLits.Nat
type instance Parse TypeLits.Nat AnyNat input = ParseNat input

type family ParseNat (input :: inputKind) :: Result TypeLits.Nat inputKind where
    ParseNat (Nat nat rest) = 'Parsed nat rest
    ParseNat anythingElse = 'NoParse

data Nat (nat :: TypeLits.Nat) (t :: Type) where
    Nat :: Proxy nat -> t -> Nat nat t

-- | A functor-like construction, where @f@ is a type constructor.
data f :<$> x

type instance ParseOutputKind ((f :: k -> outputKind) :<$> x) = outputKind
type instance Parse outputKind (f :<$> x) (input :: inputKind) =
    ParseFmap (ParseOutputKind x) input outputKind f x

type family ParseFmap outputKindX (input :: inputKind) outputKind f x :: Result outputKind inputKind where
    ParseFmap outputKindX (input :: inputKind) outputKind f x = ParseFmapFinal inputKind outputKind (Parse outputKindX x input) f

type family ParseFmapFinal inputKind outputKind parsedX f :: Result outputKind inputKind where
    ParseFmapFinal inputKind outputKind (Parsed (x :: k) remaining) (f :: k -> outputKind) = Parsed (f x) remaining
    ParseFmapFinal inputKind outputKind anything f = NoParse

-- | An applicative-like construction.
--   @Trivial@ plays the role of @pure@.
data mf :<*> mx

type instance ParseOutputKind (mf :<*> mx) =
    ParseOutputKindAp (ParseOutputKind mf) (ParseOutputKind mx)

type family ParseOutputKindAp left right :: Type where
    ParseOutputKindAp (k -> l) (k) = l

type instance Parse outputKind (mf :<*> mx) (input :: inputKind) =
    ParseApLeft (ParseOutputKind mx) inputKind outputKind mx (Parse (ParseOutputKind mx -> outputKind) mf input)

type family ParseApLeft mxKind inputKind outputKind mx parsedF :: Result outputKind inputKind where
    ParseApLeft mxKind inputKind outputKind mx (Parsed f remaining) =
        ParseApRight mxKind inputKind outputKind f (Parse mxKind mx remaining)
    ParseApLeft mxKind inputKind outputKind mx anythingElse = NoParse

type family ParseApRight mxKind inputKind outputKind f parsedX :: Result outputKind inputKind where
    ParseApRight mxKind inputKind outputKind (f :: mxKind -> outputKind) (Parsed (x :: mxKind) remaining) = Parsed (f x) remaining
    ParseApRight mxKind inputKind outputKind f anythingElse = NoParse

data f :<* x

type instance ParseOutputKind (mf :<* mx) = ParseOutputKind mf
type instance Parse outputKind (mf :<* mx) (input :: inputKind) =
    ParseLeftApLeft (ParseOutputKind mx) inputKind outputKind mx (Parse (ParseOutputKind mf) mf input)
type family ParseLeftApLeft mxKind inputKind outputKind mx parsedF :: Result outputKind inputKind where
    ParseLeftApLeft mxKind inputKind outputKind mx (Parsed f remaining) =
        ParseLeftApRight mxKind inputKind outputKind f (Parse mxKind mx remaining)
    ParseLeftApLeft mxKind inputKind outputKind mx anythingElse = NoParse
type family ParseLeftApRight mxKind inputKind outputKind f parsedX :: Result outputKind inputKind where
    ParseLeftApRight mxKind inputKind outputKind f (Parsed x remaining) = Parsed f remaining
    ParseLeftApRight mxKind inputKind outputKind f anythingElse = NoParse

data f :*> x

type instance ParseOutputKind (mf :*> mx) = ParseOutputKind mx
type instance Parse outputKind (mf :*> mx) (input :: inputKind) =
    ParseRightApLeft (ParseOutputKind mx) inputKind outputKind mx (Parse (ParseOutputKind mf) mf input)
type family ParseRightApLeft mxKind inputKind outputKind mx parsedF :: Result outputKind inputKind where
    ParseRightApLeft mxKind inputKind outputKind mx (Parsed f remaining) =
        ParseRightApRight mxKind inputKind outputKind f (Parse mxKind mx remaining)
    ParseRightApLeft mxKind inputKind outputKind mx anythingElse = NoParse
type family ParseRightApRight mxKind inputKind outputKind f parsedX :: Result outputKind inputKind where
    ParseRightApRight mxKind inputKind outputKind f (Parsed x remaining) = Parsed x remaining
    ParseRightApRight mxKind inputKind outputKind f anythingElse = NoParse

-- | An alternative-like construction.
--   @Empty@ plays the role of @empty@.
data mf :<|> mx

type instance ParseOutputKind (mf :<|> mx) = ParseOutputKind mf
type instance Parse outputKind (mf :<|> mx) (input :: inputKind) =
    ParseAltLeft (ParseOutputKind mx) inputKind outputKind input mx (Parse (ParseOutputKind mf) mf input)
type family ParseAltLeft mxKind inputKind outputKind input mx parseF :: Result outputKind inputKind where
    ParseAltLeft mxKind inputKind outputKind input mx (Parsed f remaining) = Parsed f remaining
    ParseAltLeft mxKind inputKind outputKind input mx NoParse = ParseAltRight mxKind inputKind outputKind (Parse mxKind mx input)
type family ParseAltRight mxKind inputKind outputKind parseX :: Result outputKind inputKind where
    ParseAltRight mxKind inputKind outputKind (Parsed x remaining) = Parsed x remaining
    ParseAltRight mxKind inputKind outputKind NoParse = NoParse

-- Laziness at the type level.
--
-- We wish to write recursive parsers, but we must avoid infinite types.
-- To achieve this, we introduce the notion of a type-level suspension, giving
-- laziness at the type level. A type plays the role of a thunk by giving a
-- clause for the type family Force. The type @Suspend ty k@ indicates
-- that @ty@ should be forced to something of kind @k@.

-- | This type indicates that you should use @Force ty k@ to force a new
--   type (@ty@ is a thunk).
data Suspend ty k

class Thunk (ty :: l) (resultKind :: k) where
    type Force ty (resultKind :: k) :: k

-- | We require the programmar to explicitly indicate the output kind of
--   a suspended parser, otherwise we would have to do lots and lots of work to
--   try and compute it without producing an infinite type.
data SuspendParser ty k outputKind

type instance ParseOutputKind (SuspendParser ty k outputKind) = outputKind
type instance Parse outputKind (SuspendParser ty k outputKind) (input :: inputKind) = Parse outputKind (Force ty k) input

data List (t :: k) where
    Nil :: List t
    Cons :: t -> List t -> List t

-- | 0 or more occurrences of a parser.
--   Could just as well say
--
--     @Many t = SuspendParser (ManyThunk t) Type (List r)@
--
type Many t = Force (ManyThunk t) Type

data ManyThunk (t :: Type)
instance Thunk (ManyThunk t) Type where
    type Force (ManyThunk t) Type =
        -- Must give the signature for Cons, otherwise it will default
        -- to Any -> List Any -> List Any and our type families will fail to
        -- match.
        (   ((Cons :: ParseOutputKind t -> List (ParseOutputKind t) -> List (ParseOutputKind t)) :<$> t)
            -- Observe how we recurse wile avoiding the infinite type: we
            -- give a SuspendParser, writing the same type which, when Force'd,
            -- will repeat this parser. The second argument indicates that the
            -- type of the type, when forced, is Type. More important is the
            -- third argument, which indicates the output kind of the resulting
            -- parser.
            :<*> (SuspendParser (ManyThunk t) Type (List (ParseOutputKind t)))
        )
        -- Must give the signature here, otherwise GHC will choose Any and
        -- it will kill our type families, which must match output kinds.
        :<|> Trivial (Nil :: List (ParseOutputKind t))

-- For the Many1 parser, we shall require a nonempty list.
data NonEmptyList (t :: k) where
    NonEmptyList :: t -> List t -> NonEmptyList t

-- | 1 or more occurrences of a paser.
type Many1 t = (('NonEmptyList :: ParseOutputKind t -> List (ParseOutputKind t) -> NonEmptyList (ParseOutputKind t)) :<$> t) :<*> Many t

-- | 1 or more occurrences of @t@, interspersed by @s@.
type SepBy t s = (('NonEmptyList :: ParseOutputKind t -> List (ParseOutputKind t) -> NonEmptyList (ParseOutputKind t)) :<$> t) :<*> Many (s :*> t)
