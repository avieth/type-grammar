{-|
Module      : 
Description : 
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

import Data.Kind
import Data.Proxy

import qualified GHC.TypeLits as TypeLits (Nat, Symbol)

data Result (output :: o) (input :: i) where
    NoParse :: Result output input
    Parsed :: output -> input -> Result output input

--   The family Parse means that @ty@, the parser, will take a type @input@ of
--   kind @i@, and give a @Result@ with the remaining input (has the same
--   kind as the input) and a type of the @outputKind@.
--
--   This is in direct analogy to the canonical term parser. Stating
--
--     newtype Parser input outputType = Parser (input -> Maybe (outputType, input))
--
--   is to state that, if parserType :: Parser input outputType, then
--
--     parser -> (input -> Maybe (outputType, input))
--
--   Now replace types with kinds and we have
--
--     parserType :: p -> (i -> Maybe (output :: outputKind, i))
--
--   Or something like that. TODO make this clearer.

type family ParseOutputKind ty :: Type
type family Parse (outputKind :: k) ty (input :: inputKind) :: Result outputKind inputKind

-- | The empty parser never parses. This is like @empty@ from @Alternative@.
data Empty
type instance ParseOutputKind Empty = Type
type instance Parse outputKind Empty input = NoParse

-- | The trivial parser always parses, giving @t@ and consuming no input.
--   This is like @pure@.
data Trivial (t :: k)
type instance ParseOutputKind (Trivial (t :: k)) = k
type instance Parse k (Trivial (t :: k)) (input :: inputKind) = Parsed t input


-- To make parsers which actually consume input, we'll need to be able to
-- get the head and tail of the input. This is given by the family
--
--     SplitTypeStream streamType element stream
--
-- A stream is determined by a new type, streamType, and the latter two
-- parameters describe the elements of the stream (things which can be taken
-- from the stream), and the stream itself. For example, element ~ k and
-- stream ~ [k] makes sense.

-- TBD ditch TypeStream? All we really want is a Type composed of Type -> Type.

{-
class TypeStream (streamType :: s) (element :: *) (stream :: k) where
    type SplitTypeStream (streamType :: s) (element :: *) (stream :: k) :: Maybe (element, k)

-- | A TypeStream which uses a type-level list.
data TSList k

instance TypeStream (TSList k) k ('[] :: [k]) where
    type SplitTypeStream (TSList k) k ('[] :: [k]) = 'Nothing

instance TypeStream (TSList k) k ((a ': as) :: [k]) where
    type SplitTypeStream (TSList k) k ((a ': as) :: [k]) = 'Just '(a, as)

-- | A TypeStream which uses a type-level function k -> k.
--   The second component picks out a terminal symbol. Once we encounter this,
--   the stream is considered to be EOF and no new characters are produced.
data TSConstructors k (terminal :: k)

type family TSConstructorsTerminalMatch k (terminal :: k) (candidate :: k) :: Bool where
    TSConstructorsTerminalMatch k (terminal :: k) (terminal :: k) = 'True
    TSConstructorsTerminalMatch k (terminal :: k) (anything :: k) = 'False

type family TSConstructorsSplit k (match :: Bool) (stream :: k) :: Maybe (k -> k, k) where
    TSConstructorsSplit k 'True stream = 'Nothing
    TSConstructorsSplit k 'False ((ty :: k -> k) (rest :: k)) = 'Just '(ty, rest)

-- For sequences of type constructors, as inferred from sequences of data
-- constructors in the old version.
--
-- Here we must choose a single kind, because we demand that @rest@ and
-- @ty rest@ have the same kind. So we could not choose, for example, the
-- more general @k -> l@ as the first parameter.
instance TypeStream (TSConstructors k terminal) (k -> k) (stream :: k) where
    type SplitTypeStream (TSConstructors k terminal) (k -> k) (stream :: k) =
        TSConstructorsSplit k (TSConstructorsTerminalMatch k terminal stream) stream

-- With TypeStream in place, we can give our first input-consuming parser!

-- | Match a particular character in a stream.
data Match stream character

type instance ParseOutputKind (Match stream (character :: c)) = c
type instance Parse c (Match stream (character :: c)) (input :: inputKind) =
    ParseMatch character (SplitTypeStream stream c input)

type family ParseMatch (character :: c) (maybe :: Maybe (a, b)) :: Result a b where
    ParseMatch character ('Just '(character, b)) = 'Parsed character b
    ParseMatch character anythingElse = 'NoParse
-}

-- | Match a particular type from a stream. If the head of the stream is
--   @character rest@ then it matches. Anything else and it does not.
data Match character

type instance ParseOutputKind (Match (character :: c)) = c
type instance Parse c (Match (character :: c)) (input :: inputKind) =
    ParseMatch character input

type family ParseMatch (character :: c) (input :: inputKind) :: Result c inputKind where
    ParseMatch character (character rest) = 'Parsed character rest
    ParseMatch character anythingElse = 'NoParse

-- We need special cases to match parameterized types. We can match a particular
-- Symbol by using Sym sym in Match, but to match *any* Symbol, we provide the
-- parser AnySym.

data Sym (sym :: TypeLits.Symbol) (t :: Type) where
    Sym :: Proxy sym -> t -> Sym sym t

data AnySym
type instance ParseOutputKind AnySym = TypeLits.Symbol
type instance Parse TypeLits.Symbol AnySym input = ParseSymbol input

type family ParseSymbol (input :: inputKind) :: Result TypeLits.Symbol inputKind where
    ParseSymbol (Sym sym rest) = 'Parsed sym rest
    ParseSymbol anythingElse = 'NoParse

data Nat (nat :: TypeLits.Nat) (t :: Type) where
    Nat :: Proxy nat -> t -> Nat nat t

data AnyNat
type instance ParseOutputKind AnyNat = TypeLits.Nat
type instance Parse TypeLits.Nat AnyNat input = ParseNat input

type family ParseNat (input :: inputKind) :: Result TypeLits.Nat inputKind where
    ParseNat (Nat nat rest) = 'Parsed nat rest
    ParseNat anythingElse = 'NoParse

-- We can obtain a functor-like construction by defining a new type to
-- represent @fmap@.

data f :<$> x

type instance ParseOutputKind ((f :: k -> outputKind) :<$> x) = outputKind
type instance Parse outputKind (f :<$> x) (input :: inputKind) =
    ParseFmap (ParseOutputKind x) input outputKind f x

type family ParseFmap outputKindX (input :: inputKind) outputKind f x :: Result outputKind inputKind where
    ParseFmap outputKindX (input :: inputKind) outputKind f x = ParseFmapFinal inputKind outputKind (Parse outputKindX x input) f

type family ParseFmapFinal inputKind outputKind parsedX f :: Result outputKind inputKind where
    ParseFmapFinal inputKind outputKind (Parsed (x :: k) remaining) (f :: k -> outputKind) = Parsed (f x) remaining
    ParseFmapFinal inputKind outputKind anything f = NoParse

-- To give an applicative combinator, it would be very convenient if the
-- parser and the input jointly determined the output kind. 
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

data R (t :: Type -> Type) (s :: Type)
data End = End
type Ex1 = (R :<$> Match Maybe) :<*> Trivial Int

-- There you have it! Applicative parsers at the type level :)
--
-- :kind! Parse Type Ex1 (Maybe End)
-- Parse Type Ex1 (Maybe End) :: Result * *
-- = 'Parsed (R Maybe Int) End

-- Now, we should be able to derive analogues of <* and *> by fmapping some
-- analgoue of const or flip const.
-- But maybe it's not possible! At least, I see no straightforward way of
-- doing it.

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

-- Interesting examples. The parsers on either side of the operators produce
-- different output kinds!
-- We can of course compute their output kinds using ParseOutputKind, so
-- there's no worry of mistakenly choosing the wrong kind:
--
--   :kind! Parse (ParseOutputKind Ex2) Ex2 (Maybe End)
--   = 'Parsed Maybe End
--
--   :kind! Parse (ParseOutputKind Ex3) Ex3 (Maybe End)
--   = 'Parsed Int End
--
type Ex2 = (Match Maybe) :<* Trivial Int
type Ex3 = (Match Maybe) :*> Trivial Int

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

data Q (t :: Type)
type Ex4 = (Match Maybe) :<|> (Match Q)

-- Laziness at the type level.
--
-- We wish to write recursive parsers, but we must avoid infinite types.
-- To achieve this, we introduce the notion of a type-level suspension, giving
-- laziness at the type level. A type plays the role of a thunk by giving a
-- clause for the type family Force. The type @Suspend ty k@ indicates
-- that @ty@ should be forced to something of kind @k@.

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

-- Could just as well say
--
--   Many t = SuspendParser (ManyThunk t) Type (List r)
--
-- There should be no observable difference.
type Many t = Force (ManyThunk t) Type

data ManyThunk (t :: Type)
instance Thunk (ManyThunk t) Type where
    type Force (ManyThunk t) Type =
        -- Must give the signature for Cons, otherwise it will default
        -- to Any -> List Any -> List Any and our type families will fail to
        -- match.
        (   ((Cons :: ParseOutputKind t -> List (ParseOutputKind t) -> List (ParseOutputKind t)) :<$> t)
            -- Observe how we recurse wile avoiding the infinite type: we
            -- give a Suspend, writing the same type which, when Force'd, will
            -- repeat this parser. The second argument indicates that the
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

-- Must be explicit in the type of the thing we're fmapping.
type Many1 t = (('NonEmptyList :: ParseOutputKind t -> List (ParseOutputKind t) -> NonEmptyList (ParseOutputKind t)) :<$> t) :<*> Many t

type Ex5 = Many1 (Match Maybe)

type SepBy t s = (('NonEmptyList :: ParseOutputKind t -> List (ParseOutputKind t) -> NonEmptyList (ParseOutputKind t)) :<$> t) :<*> Many (s :*> t)

type Ex6 = SepBy (Match Maybe) (Match [])

-- Attempt at a particular infix grammar: plus and times over naturals.
-- We wish to parse it from a TSConstructors Type End. What type are we
-- trying to parse? How about this one:
data GS where
    GSPlus :: GSLeftAssoc -> GS
    GSTimes :: GSLeftAssoc -> GS
    GSNumber :: TypeLits.Nat -> GS

data GSThunk
instance Thunk GSThunk Type where
    type Force GSThunk Type = GS1

data Plus (t :: Type) = Plus t
data Times (t :: Type) = Times t
data OpenParen (t :: Type) = OpenParen t
data CloseParen (t :: Type) = CloseParen t

data GSLeftAssoc where
    GSLeftAssoc :: List GS -> GS -> GSLeftAssoc

type GS1 = 'GSPlus :<$> (('GSLeftAssoc :<$> (Many (GS2 :<* (Match Plus)))) :<*> GS2)
type GS2 = 'GSTimes :<$> (('GSLeftAssoc :<$> (Many (GS3 :<* (Match Times)))) :<*> GS3)
type GS3 =      ('GSNumber :<$> AnyNat)
           :<|> (     (Match OpenParen)
                  :*> (SuspendParser GSThunk Type GS)
                  :<* (Match CloseParen)
                )

-- 1 + 2 + 3 + 4 * 5 * 6 + 7
-- 1 + 2 + 3 + ((4 * 5) * 6) + 7
-- (((1 + 2) + 3) + ((4 * 5) * 6) + 7)
type BigTerm = Nat 1 (Plus (Nat 2 (Plus (Nat 3 (Plus (Nat 4 (Times (Nat 5 (Times (Nat 6 (Plus (Nat 7 End))))))))))))

q :: Proxy (Parse GS GS1 BigTerm)
q = Proxy

r = Nat one . Plus . Nat two . Plus . OpenParen . Nat three . Plus . Nat four . Times . Nat five . Times . Nat six . Plus . Nat seven . CloseParen $ End
  where
    one :: Proxy 1
    one = Proxy
    two :: Proxy 2
    two = Proxy
    three :: Proxy 3
    three = Proxy
    four :: Proxy 4
    four = Proxy
    five :: Proxy 5
    five = Proxy
    six :: Proxy 6
    six = Proxy
    seven :: Proxy 7
    seven = Proxy
    eight :: Proxy 8
    eight = Proxy

-- Having this yields 1,505 types, and 694 coercions.
-- This blows up to 4,002, ~1,234 after simplification, even on -O0
t :: forall r . r -> Proxy (Parse GS GS1 r)
t _ = Proxy

u = t r

-- Having this yields 2,180 types and !!!!! 154,411 coericions!!!!
-- Damn that type equality constraint is EXPENSIVE!
--s :: forall r q . (q ~ Parse GS GS1 r) => r -> Proxy q
--s _ = Proxy
--
--u = s r

-- This shows promise. It's way faster and more compact than the existing
-- work in grammar. Also easier to follow I think.
-- How can we generalize it to arbitrarily many precedence levels and
-- left-, right-, non-associative operators?


-- If you parse a Singleton, you can grab its value.

class Singleton (t :: *) where
    singleton :: Proxy t -> t

instance Singleton () where
    singleton _ = ()
