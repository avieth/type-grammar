{-|
Module      : Data.Type.Grammar
Description : Type-level parsing.
Copyright   : (c) Alexander Vieth, 2015
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE AutoDeriveTypeable #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RankNTypes #-}

module Data.Type.Grammar where

import Data.List (intercalate)
import Data.Proxy

-- The idea is to use datatype of kind * -> * as symbols in our EDSLs, and
-- construct composite terms via ordinary function composition using their
-- (singleton) constructors. Things like
--
--   SELECT . :*: . FROM . TABLE theTable . WHERE . FIELD id . :=: . VALUE someId
--
-- Precisely which of these constructions are well-formed is decided through
-- a grammar, which ought to resemble at least in form the grammars given by,
-- for instance, the PostgreSQL documentation.
-- With a grammar type in hand, we should automatically recover a function
--
--   injGrammar :: MatchesGrammar ty grammar => ty -> Grammar grammar
--
-- Functions on the terms (types) of the grammar are then defined on the
-- Grammar grammar type.
--


-- Grammar types are lists whose members are any of these four types.
-- The order of the list is of course essential to the grammar.
--
type CompositeExpression = AllOf '[
      Symbol OpenParens
    , Recurse
    , Symbol CloseParens
    , OneOf '[ Symbol Plus, Symbol Times ]
    , Symbol OpenParens
    , Recurse
    , Symbol CloseParens
    ]
type SimpleExpression = Symbol Number
type Expression = OneOf '[
      SimpleExpression
    , CompositeExpression
    ]

data OpenParens t = OpenParens t
deriving instance Show t => Show (OpenParens t)
instance GrammarSymbol OpenParens where
    splitGrammarSymbol (OpenParens t) = t
    showGrammarSymbol _ = "("

data CloseParens t = CloseParens t
deriving instance Show t => Show (CloseParens t)
instance GrammarSymbol CloseParens where
    splitGrammarSymbol (CloseParens t) = t
    showGrammarSymbol _ = ")"

data Plus t = Plus t
deriving instance Show t => Show (Plus t)
instance GrammarSymbol Plus where
    splitGrammarSymbol (Plus t) = t
    showGrammarSymbol _ = "+"

data Times t = Times t
deriving instance Show t => Show (Times t)
instance GrammarSymbol Times where
    splitGrammarSymbol (Times t) = t
    showGrammarSymbol _ = "x"

data Number t = Number Int t
deriving instance Show t => Show (Number t)
instance GrammarSymbol Number where
    splitGrammarSymbol (Number _ t) = t
    showGrammarSymbol (Number i _) = show i

class GrammarSymbol (ty :: * -> *) where
    splitGrammarSymbol :: ty rest -> rest
    showGrammarSymbol :: forall rest . ty rest -> String

data Symbol (ty :: * -> *)
data AllOf (grammars :: [*])
data OneOf (grammars :: [*])
data Many (grammar :: *)
-- While Many is used to stipulate 0 or more occurrences of some grammar,
-- These is used to indicate precisely n occurrences of some grammar. It is
-- *not* used in the description of grammars, since AllOf captures this, but
-- *is* used as a parameter to the Grammar datatype, because once a Many has
-- been matched, we always know precisely how many of them were matched.
data These (grammar :: *) (count :: Nat)
data Recurse
data Close t

data Nat where
    Z :: Nat
    S :: Nat -> Nat

-- TBD not sure if this will prove useful.
type (left :. right) t = left (right t)

-- Indicate the end of a series of terms. It's like a full stop in an
-- English sentence.
data End = End
deriving instance Show End

-- Used to indicate that we're looking to match a grammar.
-- Compare at GrammarParse and GrammarNoParse, which indicate that we have
-- attempted to matach a grammar.
data GrammarMatch t = GrammarMatch {
      getGrammarMatch :: t
    }
deriving instance Show t => Show (GrammarMatch t)

{-
data GrammarNoMatch t = GrammarNoMatch {
      getGrammarNoMatch :: t
    }
deriving instance Show t => Show (GrammarNoMatch t)

data GrammarManyNoMatch t = GrammarManyNoMatch t
deriving instance Show t => Show (GrammarManyNoMatch t)

data GrammarAllOfNoMatch t = GrammarAllOfNoMatch t
deriving instance Show t => Show (GrammarAllOfNoMatch t)

data GrammarOneOfNoMatch t = GrammarOneOfNoMatch t
deriving instance Show t => Show (GrammarOneOfNoMatch t)

-- | We use this type to distinguish a match in a OneOf case. A similar
--   motif is *not* needed for AllOf, because in that case it's enough to
--   find a GrammarNoMatch in order to quit, whereas for OneOf it's a single
--   positive match which must control the computation.
newtype GrammarOneOfCandidate t = GrammarOneOfCandidate {
      getGrammarOneOfCandidate :: t
    }
deriving instance Show t => Show (GrammarOneOfCandidate t)

-- | Compute the unmatched suffix of @ty@ under @grammar@.
--   It's analogous to pure functional string parsing, in which a remaining
--   string is returned along with the parsed data. Think of this as a type
--   level function to compute just the remaining unparsed string.
--
--   Calling this, you must wrap @ty@ in @GrammarMatch@.
--   Also, you should have @recursion ~ grammar@
type family SplitGrammarK (recursion :: *) (ty :: *) (grammar :: *) :: * where

    -- The base case: symbol matching. The remaining portion is whatever is
    -- found under the symbol's type constructor.
    --SplitGrammarK (GrammarMatch End) (Symbol ty) = GrammarNoMatch End
    SplitGrammarK recursion (GrammarMatch (ty rest)) (Symbol ty) = GrammarMatch rest
    SplitGrammarK recursion (GrammarMatch ty) (Symbol ty') = GrammarNoMatch ty

    -- This case must be a recursive call (never give GrammarNoMatch as input
    -- to this type family yourself, that's understood). That's to say, some
    -- SplitGrammarK determined there's no match for @grammar@, but since
    -- this is @Many grammar@ we give @GrammarMatch ty@, because @Many@ is 0
    -- or more occurrences.
    SplitGrammarK recursion (GrammarNoMatch ty) (Many grammar) = GrammarMatch ty
    SplitGrammarK recursion (GrammarMatch ty) (Many grammar) =
        SplitGrammarK recursion (SplitGrammarK recursion (GrammarMatch ty) grammar) (Many grammar)

    SplitGrammarK recursion (GrammarMatch ty) (AllOf anything) =
        SplitGrammarAllOfK recursion (GrammarMatch ty) (AllOf anything) ty

    -- Notice the use of GrammarOneOfCandidate for the call to
    -- SplitGrammarOneOfK. This allows that family to use GrammarMatch in its
    -- call back to SplitGrammarK as an indication of a positive match, as
    -- distinct from a GrammarOneOfCandidate which indicates an initial call
    -- from this family.
    SplitGrammarK recursion (GrammarMatch ty) (OneOf anything) =
        SplitGrammarOneOfK recursion (GrammarOneOfCandidate ty) (OneOf anything) (GrammarNoMatch ty)

    SplitGrammarK recursion (GrammarMatch ty) Recurse =
        SplitGrammarK recursion (GrammarMatch ty) recursion

    SplitGrammarK recursion (GrammarMatch ty) (Close grammar) =
        SplitGrammarK grammar (GrammarMatch ty) grammar

-- | SplitGrammarK specialized for the AllOf case. Takes an extra parameter,
--   the initial first argument, so that if any match of any component of the
--   AllOf fails, it can return the initial candidate.
type family SplitGrammarAllOfK (recursion :: *) (ty :: *) (grammar :: *) (initial :: *) :: * where

    SplitGrammarAllOfK recursion (GrammarNoMatch ty) anything initial = GrammarNoMatch initial
    -- Everything matches the trivial grammar AllOf '[]
    SplitGrammarAllOfK recursion (GrammarMatch ty) (AllOf '[]) initial = GrammarMatch ty
    SplitGrammarAllOfK recursion (GrammarMatch ty) (AllOf (piece ': pieces)) initial =
        SplitGrammarAllOfK recursion (SplitGrammarK recursion (GrammarMatch ty) piece) (AllOf pieces) initial

-- | SplitGrammarK specialized for the OneOf case. Takes an extra parameter,
--   the continuation to use in case of failure.
type family SplitGrammarOneOfK (recursion :: *) (ty :: *) (grammar :: *) (continuation :: *) :: * where

    SplitGrammarOneOfK recursion (GrammarNoMatch ty) anything continuation = continuation
    SplitGrammarOneOfK recursion (GrammarMatch ty) anything continuation = GrammarMatch ty
    -- Nothing matches the empty grammar OneOf '[].
    SplitGrammarOneOfK recursion (GrammarOneOfCandidate ty) (OneOf '[]) continuation = GrammarNoMatch ty
    SplitGrammarOneOfK recursion (GrammarOneOfCandidate ty) (OneOf (piece ': pieces)) continuation =
        SplitGrammarOneOfK (recursion)
                           (SplitGrammarK recursion (GrammarMatch ty) piece)
                           (OneOf pieces) -- This parameter doesn't even matter.
                                          -- If SplitGrammarK matches, we discard it,
                                          -- and if it doesn't match, we just go to
                                          -- the continuation.
                           (SplitGrammarOneOfK recursion (GrammarOneOfCandidate ty) (OneOf pieces) continuation)

--type SplitGrammarT ty grammar = SplitGrammarK (GrammarMatch ty) grammar

-- | A class to mirror SplitGrammarK. This one gives the value of the unmatched
--   part.
class SplitGrammar recursion ty grammar where
    splitGrammar
        :: Proxy recursion
        -> ty
        -> Proxy grammar
        -> SplitGrammarK recursion ty grammar

instance {-# OVERLAPS #-}
    ( GrammarSymbol ty
    ) => SplitGrammar recursion (GrammarMatch (ty rest)) (Symbol ty)
  where
    splitGrammar _ ty _ = GrammarMatch (splitGrammarSymbol (getGrammarMatch ty))

instance {-# OVERLAPS #-}
    ( SplitGrammarK recursion (GrammarMatch ty) (Symbol ty') ~ GrammarNoMatch ty
    ) => SplitGrammar recursion (GrammarMatch ty) (Symbol ty')
  where
    splitGrammar _ ty _ = GrammarNoMatch (getGrammarMatch ty)

-- Many
--
--   SplitGrammarK (GrammarNoMatch ty) (Many grammar) = GrammarMatch ty
--
instance
    (
    ) => SplitGrammar recursion (GrammarNoMatch ty) (Many grammar)
  where
    splitGrammar _ (GrammarNoMatch ty) _ = GrammarMatch ty

--   SplitGrammarK recursion (GrammarMatch ty) (Many grammar) =
--       SplitGrammarK recursion (SplitGrammarK recursion (GrammarMatch ty) grammar) (Many grammar)
instance
    ( SplitGrammar recursion (SplitGrammarK recursion (GrammarMatch ty) grammar) (Many grammar)
    , SplitGrammar recursion (GrammarMatch ty) grammar
    ) => SplitGrammar recursion (GrammarMatch ty) (Many grammar)
  where
    splitGrammar recursion (GrammarMatch ty) proxyMany =
        splitGrammar recursion
                     (splitGrammar recursion (GrammarMatch ty) (Proxy :: Proxy grammar))
                     proxyMany

-- AllOf
--
--   SplitGrammarK recursion (GrammarMatch ty) (AllOf anything) =
--     SplitGrammarAllOfK recursion (GrammarMatch ty) (AllOf anything) ty
--
instance
    ( SplitGrammarAllOf recursion (GrammarMatch ty) (AllOf anything) ty
    ) => SplitGrammar recursion (GrammarMatch ty) (AllOf anything)
  where
    splitGrammar recursion (GrammarMatch ty) proxy = splitGrammarAllOf recursion (GrammarMatch ty) proxy ty

-- 
--  SplitGrammarAllOfK recursion (GrammarNoMatch ty) anything initial = GrammarNoMatch initial
--  SplitGrammarAllOfK recursion (GrammarMatch ty) (AllOf '[]) initial = GrammarMatch ty
--  SplitGrammarAllOfK recursion (GrammarMatch ty) (AllOf (piece ': pieces)) initial =
--      SplitGrammarAllOfK recursion (SplitGrammarK recursion (GrammarMatch ty) piece) (AllOf pieces) initial
class SplitGrammarAllOf recursion ty grammar initial where
    splitGrammarAllOf
        :: Proxy recursion
        -> ty
        -> Proxy grammar
        -> initial
        -> SplitGrammarAllOfK recursion ty grammar initial

instance
    (
    ) => SplitGrammarAllOf recursion (GrammarNoMatch ty) anything initial
  where
    splitGrammarAllOf _ (GrammarNoMatch ty) _ initial = GrammarNoMatch initial

instance
    (
    ) => SplitGrammarAllOf recursion (GrammarMatch ty) (AllOf '[]) initial
  where
    splitGrammarAllOf _ (GrammarMatch ty) _ _ = GrammarMatch ty

instance
    ( SplitGrammarAllOf recursion (SplitGrammarK recursion (GrammarMatch ty) piece) (AllOf pieces) initial
    , SplitGrammar recursion (GrammarMatch ty) piece
    ) => SplitGrammarAllOf recursion (GrammarMatch ty) (AllOf (piece ': pieces)) initial
  where
    splitGrammarAllOf recursion (GrammarMatch ty) _ initial =
        splitGrammarAllOf (recursion)
                          (splitGrammar recursion (GrammarMatch ty) (Proxy :: Proxy piece))
                          (Proxy :: Proxy (AllOf pieces))
                          (initial)

--
--  SplitGrammarK (GrammarMatch ty) (OneOf anything) =
--      SplitGrammarOneOfK (GrammarOneOfCandidate ty) (OneOf anything) (GrammarNoMatch ty)
--
instance
    ( SplitGrammarOneOf recursion (GrammarOneOfCandidate ty) (OneOf anything) (GrammarNoMatch ty)
    ) => SplitGrammar recursion (GrammarMatch ty) (OneOf anything)
  where
    splitGrammar recursion (GrammarMatch ty) proxy =
        splitGrammarOneOf (recursion)
                          (GrammarOneOfCandidate ty)
                          (proxy)
                          (GrammarNoMatch ty)

--
--  SplitGrammarOneOfK recursion (GrammarNoMatch ty) anything continuation = continuation
--  SplitGrammarOneOfK recursion (GrammarMatch ty) anything continuation = GrammarMatch ty
--  SplitGrammarOneOfK recursion (GrammarOneOfCandidate ty) (OneOf '[]) continuation = GrammarNoMatch ty
--  SplitGrammarOneOfK recursion (GrammarOneOfCandidate ty) (OneOf (piece ': pieces)) continuation =
--      SplitGrammarOneOfK (recursion)
--                         (SplitGrammarK recursion (GrammarMatch ty) piece)
--                         (OneOf pieces)
--                         (SplitGrammarOneOfK recursion (GrammarOneOfCandidate ty) (OneOf pieces) continuation)
--
class SplitGrammarOneOf recursion ty grammar continuation where
    splitGrammarOneOf
        :: Proxy recursion
        -> ty
        -> Proxy grammar
        -> continuation
        -> SplitGrammarOneOfK recursion ty grammar continuation

instance
    (
    ) => SplitGrammarOneOf recursion (GrammarNoMatch ty) anything continuation
  where
    splitGrammarOneOf _ _ _ continuation = continuation

instance
    (
    ) => SplitGrammarOneOf recursion (GrammarMatch ty) anything continuation
  where
    splitGrammarOneOf _ (GrammarMatch ty) _ _ = GrammarMatch ty

instance
    (
    ) => SplitGrammarOneOf recursion (GrammarOneOfCandidate ty) (OneOf '[]) continuation
  where
    splitGrammarOneOf _ (GrammarOneOfCandidate ty) _ _ = GrammarNoMatch ty

instance
   ( SplitGrammarOneOf (recursion)
                       (SplitGrammarK recursion (GrammarMatch ty) piece)
                       (OneOf pieces)
                       (SplitGrammarOneOfK (recursion)
                                           (GrammarOneOfCandidate ty)
                                           (OneOf pieces)
                                           (continuation)
                       )
   , SplitGrammar recursion (GrammarMatch ty) piece
   , SplitGrammarOneOf (recursion)
                       (GrammarOneOfCandidate ty)
                       (OneOf pieces)
                       (continuation)
   ) => SplitGrammarOneOf recursion (GrammarOneOfCandidate ty) (OneOf (piece ': pieces)) continuation
 where
   splitGrammarOneOf recursion (GrammarOneOfCandidate ty) _ continuation =
       splitGrammarOneOf (recursion)
                         (splitGrammar recursion (GrammarMatch ty) (Proxy :: Proxy piece))
                         (Proxy :: Proxy (OneOf pieces))
                         (splitGrammarOneOf (recursion)
                                            (GrammarOneOfCandidate ty)
                                            (Proxy :: Proxy (OneOf pieces))
                                            (continuation)
                         )

-- Recursive cases.
--
--  SplitGrammarK recursion (GrammarMatch Recurse) anything =
--      SplitGrammarK recursion (GrammarMatch recursion) anything
--
instance
    ( SplitGrammar recursion (GrammarMatch ty) recursion
    ,   SplitGrammarK recursion (GrammarMatch ty) recursion
      ~ SplitGrammarK recursion (GrammarMatch ty) Recurse
    ) => SplitGrammar recursion (GrammarMatch ty) Recurse
  where
    splitGrammar recursion (GrammarMatch ty) _  = splitGrammar recursion (GrammarMatch ty) (Proxy :: Proxy recursion)

--
--  SplitGrammarK recursion (GrammarMatch (Close ty)) anything =
--      SplitGrammarK ty (GrammarMatch ty) anything
instance
    ( SplitGrammar grammar (GrammarMatch ty) grammar
    ,   SplitGrammarK grammar (GrammarMatch ty) grammar
      ~ SplitGrammarK recursion (GrammarMatch ty) (Close grammar)
    ) => SplitGrammar recursion (GrammarMatch ty) (Close grammar)
  where
    splitGrammar _ (GrammarMatch ty) _ = splitGrammar (Proxy :: Proxy grammar) (GrammarMatch ty) (Proxy :: Proxy grammar)

splitGrammar'
    :: SplitGrammar grammar (GrammarMatch ty) grammar
    => ty
    -> Proxy grammar
    -> SplitGrammarK grammar (GrammarMatch ty) grammar
splitGrammar' ty proxyGrammar = splitGrammar proxyGrammar (GrammarMatch ty) proxyGrammar

-}

data GrammarAtom (ty :: * -> *) :: * where
    GrammarAtom :: forall ty rest . ty rest -> GrammarAtom ty

class ShowGrammarAtom ty where
    showGrammarAtom :: GrammarAtom ty -> String
instance (GrammarSymbol ty) => ShowGrammarAtom ty where
    showGrammarAtom (GrammarAtom ty) = showGrammarSymbol ty

data GrammarList (recursion :: *) (ty :: *) (count :: Nat) :: * where
    GrammarListNil :: GrammarList recursion ty Z
    GrammarListCons
        :: Grammar recursion ty
        -> GrammarList recursion ty n
        -> GrammarList recursion ty (S n)

grammarListSnoc
    :: Grammar recursion grammar
    -> GrammarList recursion grammar count
    -> GrammarList recursion grammar (S count)
grammarListSnoc g l = case l of
    GrammarListNil -> GrammarListCons g GrammarListNil
    GrammarListCons g' l' -> GrammarListCons g' (grammarListSnoc g l')

class ShowGrammarList recursion grammar count where
    showGrammarList :: GrammarList recursion grammar count -> [String]
instance ShowGrammarList recursion grammar Z where
    showGrammarList _ = []
instance 
    ( ShowGrammarList recursion grammar n
    , ShowGrammar recursion grammar
    ) => ShowGrammarList recursion grammar (S n)
  where
    showGrammarList (GrammarListCons this that) = showGrammar this : showGrammarList that

data GrammarSum (recursion :: *) (tys :: [*]) :: * where
    GrammarSumNil :: GrammarSum recursion '[]
    GrammarSumCons
        :: Either (Grammar recursion ty) (GrammarSum recursion tys)
        -> GrammarSum recursion (ty ': tys)

class ShowGrammarSum recursion grammars where
    showGrammarSum :: GrammarSum recursion grammars -> String
instance ShowGrammarSum recursion '[] where
    showGrammarSum _ = "<empty grammar>"
instance
    ( ShowGrammarSum recursion grammars
    , ShowGrammar recursion grammar
    ) => ShowGrammarSum recursion (grammar ': grammars)
  where
    showGrammarSum (GrammarSumCons sum) = case sum of
        Left here -> showGrammar here
        Right there -> showGrammarSum there

class GrammarSumInject (recursion :: *) (grammar :: *) (grammars :: [*]) where
    grammarSumInject
        :: Proxy recursion
        -> Proxy grammars
        -> Grammar recursion grammar
        -> GrammarSum recursion grammars
instance {-# OVERLAPS #-}
    (
    ) => GrammarSumInject recursion grammar (grammar ': grammars)
  where
    grammarSumInject _ _ grammar = GrammarSumCons (Left grammar)
instance
    ( GrammarSumInject recursion grammar grammars
    ) => GrammarSumInject recursion grammar (other ': grammars)
  where
    grammarSumInject recursion _ grammar =
        GrammarSumCons (Right (grammarSumInject recursion (Proxy :: Proxy grammars) grammar))

data GrammarProduct (recursion :: *) (tys :: [*]) :: * where
    GrammarProductNil :: GrammarProduct recursion '[]
    GrammarProductCons
        :: (Grammar recursion ty, GrammarProduct recursion tys)
        -> GrammarProduct recursion (ty ': tys)

grammarProductSnoc
    :: Grammar recursion grammar
    -> GrammarProduct recursion grammars
    -> GrammarProduct recursion (Snoc grammar grammars)
grammarProductSnoc grammar grammars = case grammars of
    GrammarProductNil -> GrammarProductCons (grammar, GrammarProductNil)
    GrammarProductCons (grammar', grammars') ->
        GrammarProductCons (grammar', grammarProductSnoc grammar grammars')

type family Snoc x xs where
    Snoc x '[] = '[x]
    Snoc x (y ': ys) = y ': Snoc x ys

class ShowGrammarProduct recursion grammars where
    showGrammarProduct :: GrammarProduct recursion grammars -> String
instance ShowGrammarProduct recursion '[] where
    showGrammarProduct _ = ""
instance
    ( ShowGrammarProduct recursion grammars
    , ShowGrammar recursion grammar
    ) => ShowGrammarProduct recursion (grammar ': grammars)
  where
    showGrammarProduct (GrammarProductCons (here, there)) =
        showGrammar here ++ showGrammarProduct there

-- | This type is composed of all parses of @grammar@ relative to @recursion@.
data Grammar (recursion :: *) (grammar :: *) :: * where
    -- Interesting use of an existential here. You don't get to use the
    -- tail of the symbol, on data inherent to the symbol (if any).
    GrammarSymbol :: GrammarAtom ty -> Grammar recursion (Symbol ty)
    GrammarMany :: GrammarList recursion ty count -> Grammar recursion (These ty count)
    GrammarAllOf :: GrammarProduct recursion grammars -> Grammar recursion (AllOf grammars)
    GrammarOneOf :: GrammarSum recursion grammars -> Grammar recursion (OneOf grammars)
    GrammarRecurse :: Grammar recursion recursion -> Grammar recursion Recurse
    GrammarClose :: Grammar grammar grammar -> Grammar recursion (Close grammar)

class ShowGrammar recursion grammar where
    showGrammar :: Grammar recursion grammar -> String
instance
    ( ShowGrammarAtom ty
    ) => ShowGrammar recursion (Symbol ty)
  where
    showGrammar (GrammarSymbol atom) = showGrammarAtom atom
instance
    ( ShowGrammarList recursion grammar count
    ) => ShowGrammar recursion (These grammar count)
  where
    showGrammar (GrammarMany list) = concat [
          "["
        , intercalate ", " (showGrammarList list)
        , "]"
        ]
instance
    ( ShowGrammarProduct recursion grammars
    ) => ShowGrammar recursion (AllOf grammars)
  where
    showGrammar (GrammarAllOf product) =
        showGrammarProduct product
instance
    ( ShowGrammarSum recursion grammars
    ) => ShowGrammar recursion (OneOf grammars)
  where
    showGrammar (GrammarOneOf sum) = showGrammarSum sum
instance
    ( ShowGrammar recursion recursion
    ) => ShowGrammar recursion Recurse
  where
    showGrammar (GrammarRecurse rec) = showGrammar rec
instance
    ( ShowGrammar grammar grammar
    ) => ShowGrammar recursion (Close grammar)
  where
    showGrammar (GrammarClose clo) = showGrammar clo

-- What's the plan?
-- SplitGrammarK is instructive. Shows us how to come up with the tail portion
-- of the grammar. BUT we need something more, something which is even more
-- directly analagous to pure functional parsers.
--
--   type Parser a t = a -> Maybe (t, a)
--
-- We shall need different forms for our combinators
--
--   ParserMany t ~ Maybe ( '[t], rest )
--
-- Ultimately we shall need the matching type classes. What will they look
-- like? Surely we want the range types of ParseGrammar to be
--
--   GrammarSymbol symbol
--   GrammarMany grammar
--   GrammarAllOf grammars
--   GrammarOneOf grammars
--
data GrammarParse recursion grammar remainder where
    GrammarParse
        :: Grammar recursion grammar
        -> remainder
        -> GrammarParse recursion grammar remainder

data GrammarNoParse = GrammarNoParse

type family ParseGrammarK (recursion :: *) (ty :: *) (grammar :: *) :: * where

    ParseGrammarK recursion (GrammarMatch (ty rest)) (Symbol ty) =
        GrammarParse recursion (Symbol ty) rest
    ParseGrammarK recursion (GrammarMatch ty) (Symbol ty') =
        GrammarNoParse

    ParseGrammarK recursion (GrammarMatch ty) (Many grammar) =
        ParseGrammarManyK recursion
                          (GrammarMatch ty)
                          (Many grammar)
                          -- Note the use of These rather than Many.
                          -- It'd odd, but Many does not parameterize a
                          -- Grammar value; instead, we use These because it
                          -- contains a count of how many grammar were matched.
                          (GrammarParse recursion (These grammar Z) ty)

    ParseGrammarK recursion (GrammarMatch ty) (AllOf grammars) =
        ParseGrammarAllOfK (recursion)
                           (GrammarMatch ty)
                           (AllOf grammars)
                           (GrammarParse recursion (AllOf '[]) ty)

    ParseGrammarK recursion (GrammarMatch ty) (OneOf grammars) =
        ParseGrammarOneOfK (recursion) 
                           (GrammarMatch ty)
                           (OneOf grammars)
                           (ty)
                           (OneOf grammars)

    -- When we recurse, we must remember to, in case of a match, replace
    -- the type parameter with Recurse.
    --ParseGrammarK recursion anything Recurse =
    --    ParseGrammarK recursion anything recursion
    ParseGrammarK recursion anything Recurse =
        ParseGrammarRecurseK recursion anything Recurse

    -- This will cause trouble. If there's a Close in an AllOf/OneOf/Many,
    -- we're going to recover a different recursion reference.
    -- If this one parses, we need to replace the parameter...
    --ParseGrammarK recursion anything (Close grammar) =
    --    ParseGrammarK grammar anything grammar
    ParseGrammarK recursion anything (Close grammar) =
        ParseGrammarCloseK recursion anything (Close grammar)

type family ParseGrammarRecurseK (recursion :: *) (ty :: *) (grammar :: *) :: * where

    ParseGrammarRecurseK recursion (GrammarParse recursion recursion rest) Recurse =
        GrammarParse recursion Recurse rest

    ParseGrammarRecurseK recursion GrammarNoParse Recurse = GrammarNoParse

    ParseGrammarRecurseK recursion (GrammarMatch ty) Recurse =
        ParseGrammarRecurseK (recursion)
                             (ParseGrammarK recursion (GrammarMatch ty) recursion)
                             (Recurse)

type family ParseGrammarCloseK (recursion :: *) (ty :: *) (grammar :: *) :: * where

    ParseGrammarCloseK recursion (GrammarParse grammar grammar rest) (Close grammar) =
        GrammarParse recursion (Close grammar) rest

    ParseGrammarCloseK recursion GrammarNoParse (Close grammar) = GrammarNoParse

    -- Called from ParseGrammarK: try to parse with the new recursion reference.
    -- The above two cases will collect the output and in case of a parse,
    -- replace the recursion reference.
    ParseGrammarCloseK recursion (GrammarMatch ty) (Close grammar) =
        ParseGrammarCloseK (recursion)
                           (ParseGrammarK grammar (GrammarMatch ty) grammar)
                           (Close grammar)

type family ParseGrammarManyK (recursion :: *) (ty :: *) (grammar :: *) (initial :: *) :: * where

    ParseGrammarManyK recursion GrammarNoParse (Many grammar) initial = initial

    ParseGrammarManyK recursion (GrammarParse recursion this rest) (Many grammar) (GrammarParse recursion (These grammar count) ty) =
        ParseGrammarManyK (recursion)
                          (ParseGrammarK recursion (GrammarMatch rest) grammar)
                          (Many grammar)
                          (GrammarParse recursion (These grammar (S count)) rest)

    -- The entry point. Try matching against the grammar to recover either
    -- GrammarNoParse or GrammarParse, and feed that back into ParseGrammarManyK
    -- so we can decide what to do next.
    ParseGrammarManyK recursion (GrammarMatch ty) (Many grammar) initial =
        ParseGrammarManyK (recursion)
                          (ParseGrammarK recursion (GrammarMatch ty) grammar)
                          (Many grammar)
                          (initial)

type family ParseGrammarAllOfK (recursion :: *) (ty :: *) (grammar :: *) (initial :: *) :: * where

    -- A no parse for any of the AllOf grammars kills the whole parse.
    ParseGrammarAllOfK recursion (GrammarNoParse) (AllOf anything) initial =
        GrammarNoParse

    ParseGrammarAllOfK recursion (GrammarParse recursion this rest) (AllOf grammars) (GrammarParse recursion (AllOf parsed) rest') =
        ParseGrammarAllOfK (recursion)
                           (GrammarMatch rest)
                           (AllOf grammars)
                           -- It's important to Snoc, so that we get the
                           -- order right. @parsed@ represnts things already
                           -- parsed, so they should come before @this@, so
                           -- that the left-to-right order of a corresponding
                           -- GrammarProduct is the left-to-right order of
                           -- the grammar.
                           (GrammarParse recursion (AllOf (Snoc this parsed)) rest)

    -- The trivial grammar AllOf '[] always parses.
    ParseGrammarAllOfK recursion (GrammarMatch ty) (AllOf '[]) (GrammarParse recursion (AllOf parsed) ty) =
        GrammarParse recursion (AllOf parsed) ty

    -- Parse the first grammar and feeds its result back into this function.
    ParseGrammarAllOfK recursion (GrammarMatch ty) (AllOf (grammar ': grammars)) initial =
        ParseGrammarAllOfK (recursion)
                           (ParseGrammarK recursion (GrammarMatch ty) (grammar))
                           (AllOf grammars)
                           (initial)

-- For this family we need an extra parameter which remembers the recursion
-- term we're parsing, so we can reuse it on the next summands whenever one of
-- the summands fails to parse.
-- That's in addition to the other parameter which just tracks the whole
-- sum type, as we'll need to remember that as well.
type family ParseGrammarOneOfK (recursion :: *) (ty :: *) (grammar :: *) (initial :: *) (wholeSum :: *) :: * where

    -- It's important to put this clause first. It recognizes a recursive call
    -- in which some grammar parsed.
    ParseGrammarOneOfK recursion (GrammarParse recursion this rest) (OneOf grammars) initial wholeSum =
        GrammarParse recursion wholeSum rest

    -- Nothing matches the empty grammar OneOf '[]
    ParseGrammarOneOfK recursion (GrammarNoParse) (OneOf '[]) initial wholeSum =
        GrammarNoParse

    -- Something didn't parse, so try again, resetting the input to the
    -- initial.
    ParseGrammarOneOfK recursion (GrammarNoParse) (OneOf (grammar ': grammars)) initial wholeSum =
        ParseGrammarOneOfK (recursion)
                           (GrammarMatch initial)
                           (OneOf (grammar ': grammars))
                           (initial)
                           (wholeSum)

    -- Parse the first grammar and feed its result back into this function.
    -- This is the same in form as that of ParseGrammarAllOfK's last clause.
    -- It's the other clauses which set this one apart.
    ParseGrammarOneOfK recursion (GrammarMatch ty) (OneOf (grammar ': grammars)) initial wholeSum =
        ParseGrammarOneOfK (recursion)
                           (ParseGrammarK recursion (GrammarMatch ty) grammar)
                           (OneOf grammars)
                           (initial)
                           (wholeSum)


-- | Some prefix of @ty@ matches @grammar@, leaving @remainder@ unmatched.
--   The parameter @recursion@ is here for the benefit of recursion via
--   @Recure@ and @Close t@.
class ParseGrammar recursion ty grammar where
    parseGrammar
        :: Proxy recursion
        -> ty
        -> Proxy grammar
        -> ParseGrammarK recursion ty grammar

instance
    ( GrammarSymbol ty
    ) => ParseGrammar recursion (GrammarMatch (ty rest)) (Symbol ty)
  where
    parseGrammar _ (GrammarMatch tyrest) _ = GrammarParse (GrammarSymbol (GrammarAtom tyrest)) (splitGrammarSymbol tyrest)

--
--  ParseGrammarK recursion (GrammarMatch ty) (Symbol ty') =
--      GrammarNoParse
--
instance {-# OVERLAPS #-}
    ( ParseGrammarK recursion (GrammarMatch ty) (Symbol ty') ~ GrammarNoParse
    ) => ParseGrammar recursion (GrammarMatch ty) (Symbol ty')
  where
    parseGrammar _ _ _ = GrammarNoParse

-- Many

{-
 - TBD should be able to safely remove this. Says the same thing as the instance
 - immediately following it, no?
instance
    ( ParseGrammarMany recursion ty (Many grammar) (GrammarParse (These grammar Z) ty)
    ,   ParseGrammarK recursion ty (Many grammar)
      ~ ParseGrammarManyK recursion ty (Many grammar) (GrammarParse (These grammar Z) ty)
    ) => ParseGrammar recursion ty (Many grammar)
  where
    parseGrammar recursion ty grammar =
        parseGrammarMany recursion
                         ty
                         grammar
                         (GrammarParse (GrammarMany (GrammarListNil :: GrammarList grammar Z)) ty)
-}

instance
    ( ParseGrammarMany recursion
                       (GrammarMatch ty)
                       (Many grammar)
                       (GrammarParse recursion (These grammar Z) ty)
    ) => ParseGrammar recursion (GrammarMatch ty) (Many grammar)
  where
    parseGrammar recursion (GrammarMatch ty) grammar =
        parseGrammarMany recursion
                         (GrammarMatch ty)
                         grammar
                         (GrammarParse (GrammarMany (GrammarListNil :: GrammarList recursion grammar Z)) ty)


-- AllOf
instance
    ( ParseGrammarAllOf recursion (GrammarMatch ty) (AllOf grammars) (GrammarParse recursion (AllOf '[]) ty)
    ) => ParseGrammar recursion (GrammarMatch ty) (AllOf grammars)
  where 
    parseGrammar recursion (GrammarMatch ty) grammar =
        parseGrammarAllOf recursion
                          (GrammarMatch ty)
                          grammar
                          (GrammarParse (GrammarAllOf (GrammarProductNil :: GrammarProduct recursion '[])) ty)

-- OneOf
instance
    ( ParseGrammarOneOf recursion (GrammarMatch ty) (OneOf grammars) ty (OneOf grammars)
    ) => ParseGrammar recursion (GrammarMatch ty) (OneOf grammars)
  where
    parseGrammar recursion (GrammarMatch ty) grammar =
        parseGrammarOneOf recursion
                          (GrammarMatch ty)
                          grammar
                          (ty)
                          grammar

-- Recurse
instance
    ( ParseGrammarRecurse recursion anything Recurse
    ) => ParseGrammar recursion anything Recurse
  where
    parseGrammar = parseGrammarRecurse

instance
    ( ParseGrammarClose recursion anything (Close grammar)
    ) => ParseGrammar recursion anything (Close grammar)
  where
    parseGrammar = parseGrammarClose

class ParseGrammarMany recursion ty grammar initial where
    parseGrammarMany
        :: Proxy recursion
        -> ty
        -> Proxy grammar
        -> initial
        -> ParseGrammarManyK recursion ty grammar initial

--  ParseGrammarManyK recursion GrammarNoParse (Many grammar) initial = initial
instance
    (
    ) => ParseGrammarMany recursion GrammarNoParse (Many grammar) initial
  where
    parseGrammarMany _ _ _ = id

--  ParseGrammarManyK recursion (GrammarParse this rest) (Many grammar) (GrammarParse (These grammar count) ty) =
--      ParseGrammarManyK (recursion)
--                        (ParseGrammarK recursion (GrammarMatch rest) grammar)
--                        (Many grammar)
--                        (GrammarParse (These grammar (count + 1)) rest)
instance
    ( ParseGrammarMany (recursion)
                       (ParseGrammarK recursion (GrammarMatch rest) grammar)
                       (Many grammar)
                       (GrammarParse recursion (These grammar (S count)) rest)
    , ParseGrammar recursion (GrammarMatch rest) grammar
    ) => ParseGrammarMany recursion (GrammarParse recursion grammar rest) (Many grammar) (GrammarParse recursion (These grammar count) ty)
  where
    parseGrammarMany recursion (GrammarParse this rest) proxyManyGrammar (GrammarParse those rest') =
        parseGrammarMany (recursion)
                         (parseGrammar recursion (GrammarMatch rest) (Proxy :: Proxy grammar))
                         proxyManyGrammar
                         (GrammarParse (GrammarMany newGrammarList) rest)
      where
        -- Careful to puut this match behind the existing matches, as it was
        -- discovered after them.
        grammarListTail :: GrammarList recursion grammar count
        grammarListTail = case those of
            GrammarMany grammarList -> grammarList
        newGrammarList :: GrammarList recursion grammar (S count)
        newGrammarList = grammarListSnoc this grammarListTail

--
--  ParseGrammarManyK recursion (GrammarMatch ty) (Many grammar) initial =
--      ParseGrammarManyK (recursion)
--                        (ParseGrammarK recursion (GrammarMatch ty) grammar)
--                        (Many grammar)
--                        (initial)
instance
    ( ParseGrammarMany (recursion)
                       (ParseGrammarK recursion (GrammarMatch ty) grammar)
                       (Many grammar)
                       initial
    , ParseGrammar recursion (GrammarMatch ty) grammar
    ) => ParseGrammarMany recursion (GrammarMatch ty) (Many grammar) initial
  where
    parseGrammarMany recursion (GrammarMatch ty) proxyManyGrammar initial =
        parseGrammarMany (recursion)
                         (parseGrammar recursion (GrammarMatch ty) (Proxy :: Proxy grammar))
                         (proxyManyGrammar)
                         (initial)

class ParseGrammarAllOf recursion ty grammar initial where
    parseGrammarAllOf
        :: Proxy recursion
        -> ty
        -> Proxy grammar
        -> initial
        -> ParseGrammarAllOfK recursion ty grammar initial

--    ParseGrammarAllOfK recursion (GrammarNoParse) (AllOf anything) initial =
--        GrammarNoParse
instance
    (
    ) => ParseGrammarAllOf recursion (GrammarNoParse) (AllOf anything) initial
  where
    parseGrammarAllOf _ _ _ _ = GrammarNoParse

--    ParseGrammarAllOfK recursion (GrammarParse recursion this rest) (AllOf grammars) (GrammarParse recursion (AllOf parsed) rest') =
--        ParseGrammarAllOfK (recursion)
--                           (GrammarMatch rest)
--                           (AllOf grammars)
--                           (GrammarParse recursion (AllOf (this ': parsed)) rest)
instance
    ( ParseGrammarAllOf recursion
                        (GrammarMatch rest)
                        (AllOf grammars)
                        (GrammarParse recursion (AllOf (Snoc this parsed)) rest)
    ) => ParseGrammarAllOf recursion (GrammarParse recursion this rest) (AllOf grammars) (GrammarParse recursion (AllOf parsed) rest')
  where
    parseGrammarAllOf recursion (GrammarParse this rest) grammar (GrammarParse parsed rest') =
        parseGrammarAllOf (recursion)
                          (GrammarMatch rest)
                          (grammar)
                          (GrammarParse (GrammarAllOf next) rest)
      where
        current :: GrammarProduct recursion parsed
        current = case parsed of
            GrammarAllOf product -> product
        next :: GrammarProduct recursion (Snoc this parsed)
        next = grammarProductSnoc this current

--    ParseGrammarAllOfK recursion (GrammarMatch ty) (AllOf '[]) (GrammarParse recursion (AllOf parsed) ty) =
--        GrammarParse recursion (AllOf parsed) ty
instance
    (
    ) => ParseGrammarAllOf recursion (GrammarMatch ty) (AllOf '[]) (GrammarParse recursion (AllOf parsed) ty)
  where
    parseGrammarAllOf recursion (GrammarMatch ty) grammar (GrammarParse parsed ty') =
        GrammarParse parsed ty'

--    ParseGrammarAllOfK recursion (GrammarMatch ty) (AllOf (grammar ': grammars)) initial =
--        ParseGrammarAllOfK (recursion)
--                           (ParseGrammarK recursion (GrammarMatch ty) (grammar))
--                           (AllOf grammars)
--                           (initial)
instance
    ( ParseGrammarAllOf recursion
                        (ParseGrammarK recursion (GrammarMatch ty) grammar)
                        (AllOf grammars)
                        initial
    , ParseGrammar recursion (GrammarMatch ty) grammar
    ) => ParseGrammarAllOf recursion (GrammarMatch ty) (AllOf (grammar ': grammars)) initial
  where
    parseGrammarAllOf recursion (GrammarMatch ty) grammar initial =
        parseGrammarAllOf recursion
                          (parseGrammar recursion (GrammarMatch ty) (Proxy :: Proxy grammar))
                          (Proxy :: Proxy (AllOf grammars))
                          initial

class ParseGrammarOneOf recursion ty grammar initial wholeSum where
    parseGrammarOneOf
        :: Proxy recursion
        -> ty
        -> Proxy grammar
        -> initial
        -> Proxy wholeSum
        -> ParseGrammarOneOfK recursion ty grammar initial wholeSum

--    ParseGrammarOneOfK recursion (GrammarParse recursion this rest) (OneOf grammars) initial wholeSum =
--        GrammarParse wholeSum rest
instance
    ( GrammarSumInject recursion this wholeSum
    ) => ParseGrammarOneOf recursion (GrammarParse recursion this rest) (OneOf grammars) initial (OneOf wholeSum)
  where
    parseGrammarOneOf _ (GrammarParse this rest) _ _ _ =
        GrammarParse (GrammarOneOf (grammarSumInject (Proxy :: Proxy recursion)
                                                     (Proxy :: Proxy wholeSum)
                                                     this
                                   )
                     ) rest

--    ParseGrammarOneOfK recursion anything (OneOf '[]) initial wholeSum =
--        GrammarNoParse
instance
    (
    ) => ParseGrammarOneOf recursion GrammarNoParse (OneOf '[]) initial wholeSum
  where
    parseGrammarOneOf _ _ _ _ _ = GrammarNoParse

--    ParseGrammarOneOfK recursion (GrammarNoParse) (OneOf grammars) initial wholeSum =
--        ParseGrammarOneOfK (recursion)
--                           (GrammarMatch initial)
--                           (OneOf grammars)
--                           (initial)
--                           (wholeSum)
instance
    ( ParseGrammarOneOf recursion
                        (GrammarMatch initial)
                        (OneOf (grammar ': grammars))
                        initial
                        wholeSum
    ) => ParseGrammarOneOf recursion GrammarNoParse (OneOf (grammar ': grammars)) initial wholeSum
  where
    parseGrammarOneOf recursion _ grammars initial wholeSum =
        parseGrammarOneOf recursion (GrammarMatch initial) grammars initial wholeSum

--    ParseGrammarOneOfK recursion (GrammarMatch ty) (OneOf (grammar ': grammars)) initial wholeSum =
--        ParseGrammarOneOfK (recursion)
--                           (ParseGrammarK recursion (GrammarMatch ty) grammar)
--                           (OneOf grammars)
--                           (initial)
--                           (wholeSum)
instance
    ( ParseGrammarOneOf recursion
                        (ParseGrammarK recursion (GrammarMatch ty) grammar)
                        (OneOf grammars)
                        initial
                        wholeSum
    , ParseGrammar recursion (GrammarMatch ty) grammar
    ) => ParseGrammarOneOf recursion (GrammarMatch ty) (OneOf (grammar ': grammars)) initial wholeSum
  where
    parseGrammarOneOf recursion (GrammarMatch ty) grammars initial wholeSum =
        parseGrammarOneOf recursion
                          (parseGrammar recursion (GrammarMatch ty) (Proxy :: Proxy grammar))
                          (Proxy :: Proxy (OneOf grammars))
                          initial
                          wholeSum

class ParseGrammarRecurse recursion ty grammar where
    parseGrammarRecurse
        :: Proxy recursion
        -> ty
        -> Proxy grammar
        -> ParseGrammarRecurseK recursion ty grammar

--    ParseGrammarRecurseK recursion (GrammarParse recursion recursion rest) Recurse =
--        GrammarParse recursion Recurse rest
instance
    (
    ) => ParseGrammarRecurse recursion (GrammarParse recursion recursion rest) Recurse
  where
    parseGrammarRecurse _ (GrammarParse grammar rest) _ =
        GrammarParse (GrammarRecurse grammar) rest

--
--    ParseGrammarRecurseK recursion GrammarNoParse Recurse = GrammarNoParse
instance
    (
    ) => ParseGrammarRecurse recursion GrammarNoParse Recurse
  where
    parseGrammarRecurse _ GrammarNoParse _ = GrammarNoParse

--    ParseGrammarRecurseK recursion (GrammarMatch ty) Recurse =
--        ParseGrammarRecurseK (recursion)
--                             (ParseGrammarK recursion (GrammarMatch ty) recursion)
--                             (Recurse)
instance
    ( ParseGrammarRecurse (recursion)
                          (ParseGrammarK recursion (GrammarMatch ty) recursion)
                          (Recurse)
    , ParseGrammar (recursion) (GrammarMatch ty) (recursion)
    ) => ParseGrammarRecurse recursion (GrammarMatch ty) Recurse
  where
    parseGrammarRecurse recursion (GrammarMatch ty) recurse =
        parseGrammarRecurse (recursion)
                            (parseGrammar recursion (GrammarMatch ty) recursion)
                            (recurse)

class ParseGrammarClose recursion ty grammar where
    parseGrammarClose
        :: Proxy recursion
        -> ty
        -> Proxy grammar
        -> ParseGrammarCloseK recursion ty grammar

--    ParseGrammarCloseK recursion (GrammarParse grammar (Close grammar) rest) (Close grammar) =
--        GrammarParse recursion (Close grammar) rest
instance
    (
    ) => ParseGrammarClose recursion (GrammarParse grammar grammar rest) (Close grammar)
  where
    parseGrammarClose _ (GrammarParse grammar rest) _ =
        GrammarParse (GrammarClose grammar) rest

--    ParseGrammarCloseK recursion GrammarNoParse (Close grammar) = GrammarNoParse
instance
    (
    ) => ParseGrammarClose recursion GrammarNoParse (Close grammar)
  where
    parseGrammarClose _ GrammarNoParse _ = GrammarNoParse

--    ParseGrammarCloseK recursion (GrammarMatch ty) (Close grammar) =
--        ParseGrammarCloseK (recursion)
--                           (ParseGrammarK grammar (GrammarMatch ty) grammar)
--                           (Close grammar)
--
instance
    ( ParseGrammarClose (recursion)
                        (ParseGrammarK grammar (GrammarMatch ty) grammar)
                        (Close grammar)
    , ParseGrammar grammar (GrammarMatch ty) grammar
    ) => ParseGrammarClose recursion (GrammarMatch ty) (Close grammar)
  where
    parseGrammarClose recursion (GrammarMatch ty) close =
        parseGrammarClose (recursion)
                          (parseGrammar (Proxy :: Proxy grammar)
                                        (GrammarMatch ty)
                                        (Proxy :: Proxy grammar)
                          )
                          (close)
