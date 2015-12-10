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

import Data.Void
import Data.Proxy
import Data.Monoid
import Data.String (IsString, fromString)

data TestSymbol (ps :: [*]) (t :: *) :: * where
    TestSymbol :: t -> TestSymbol '[] t

instance GrammarSymbol (TestSymbol ps) where
    splitGrammarSymbol (TestSymbol t) = t
    mapGrammarSymbol f (TestSymbol t) = TestSymbol (f t)

data SymbolA (ps :: [*]) (t :: *) :: * where
    SymbolA :: t -> SymbolA '[] t

instance GrammarSymbol (SymbolA ps) where
    splitGrammarSymbol (SymbolA t) = t
    mapGrammarSymbol f (SymbolA t) = SymbolA (f t)

data SymbolB (ps :: [*]) (t :: *) :: * where
    SymbolB :: t -> SymbolB '[] t

instance GrammarSymbol (SymbolB ps) where
    splitGrammarSymbol (SymbolB t) = t
    mapGrammarSymbol f (SymbolB t) = SymbolB (f t)

type family ParseDerivedGrammarK (derivedGrammar :: *) (term :: *) :: * where
    ParseDerivedGrammarK derivedGrammar term =
        ParseDerivedGrammarChooseK derivedGrammar (ParseGrammarK (DeconstructGrammar derivedGrammar)
                                                                 (GrammarMatch term)
                                                                 (DeconstructGrammar derivedGrammar)
                                                  )

class ParseDerivedGrammar (derivedGrammar :: *) (term :: *) where
    parseDerivedGrammar
        :: Proxy derivedGrammar
        -> term
        -> ParseDerivedGrammarK derivedGrammar term

instance
    ( ParseDerivedGrammarChoose derivedGrammar (ParseGrammarK (DeconstructGrammar derivedGrammar)
                                                              (GrammarMatch term)
                                                              (DeconstructGrammar derivedGrammar)
                                               )
    , ParseGrammar (DeconstructGrammar derivedGrammar)
                   (GrammarMatch term)
                   (DeconstructGrammar derivedGrammar)
    ) => ParseDerivedGrammar derivedGrammar term
  where
    parseDerivedGrammar derivedGrammar term =
        parseDerivedGrammarChoose derivedGrammar (parseGrammar primitive (GrammarMatch term) primitive)
      where
        primitive :: Proxy (DeconstructGrammar derivedGrammar)
        primitive = Proxy

type family ParseDerivedGrammarChooseK (derivedGrammar :: *) (parseResult :: *) :: * where
    ParseDerivedGrammarChooseK derivedGrammar GrammarNoParse = GrammarNoParse
    ParseDerivedGrammarChooseK derivedGrammar (GrammarParse primitiveParse remaining) =
        GrammarParse (TransitiveInferredGrammar derivedGrammar primitiveParse) remaining

class ParseDerivedGrammarChoose (derivedGrammar :: *) (parseResult :: *) where
    parseDerivedGrammarChoose 
        :: Proxy derivedGrammar
        -> parseResult
        -> ParseDerivedGrammarChooseK derivedGrammar parseResult

instance
    (
    ) => ParseDerivedGrammarChoose derivedGrammar GrammarNoParse
  where
    parseDerivedGrammarChoose _ = id

instance
    ( ReconstructInferredGrammar derivedGrammar primitiveParse
    ) => ParseDerivedGrammarChoose derivedGrammar (GrammarParse primitiveParse remaining)
  where
    parseDerivedGrammarChoose derivedGrammar parse = case parse of
        GrammarParse primitiveParse remaining -> GrammarParse inferred remaining
          where
            inferred = reconstructInferredGrammar derivedGrammar primitiveParse

-- | The output of the parse, the so-called "inferred grammar". It's like the
--   input (so-called "symbolic grammar") but with type parameters of symbols
--   inferred.
type family GrammarParseInferred (grammarParse :: *) :: * where
    GrammarParseInferred (GrammarParse parsed rest) = parsed

-- | The remainder of the parse.
type family GrammarParseRemainder (grammarParse :: *) :: * where
    GrammarParseRemainder (GrammarParse parsed remainder) = remainder

-- | This class recognizes complete parses (remainder is GEnd).
--   Assumes the convention that GEnd is always used to terminate the sequence
--   of types.
class
    ( GrammarParseRemainder (ParseGrammarK grammar term grammar) ~ GEnd
    ) => CompleteParse term grammar
instance
    ( GrammarParseRemainder (ParseGrammarK grammar term grammar) ~ GEnd
    ) => CompleteParse term grammar

-- | Anything which can be used as a symbol in a grammar. This class shows how
--   to pop it off and obtain the tail of the sequence. It's analagous to
--   a Stream typeclass which may be demanded of the input stream for a typical
--   term parser.
class GrammarSymbol (ty :: * -> *) where
    splitGrammarSymbol :: ty rest -> rest
    mapGrammarSymbol :: (rest -> rest') -> ty rest -> ty rest'

-- | It's sometimes nice to be able to print a sequence of constructors, without
--   first parsing it to a Grammar value. If every type in the sequence is
--   an instance of this class, then this can be done.
class GrammarSymbol symbol => PrintGrammarSymbol (symbol :: * -> *) (m :: *) where
    printGrammarSymbol :: Proxy m -> symbol anything -> m

-- The components of grammars.

class DerivedGrammar (derivedGrammar :: *) where
    type DerivedFrom derivedGrammar :: *

class
    ( DerivedGrammar derivedGrammar
    ) => InferredGrammar (inferredFrom :: *) (derivedGrammar :: *)
  where
    type InferredForm inferredFrom derivedGrammar :: *
    inferFromUnderlying
        :: Proxy derivedGrammar
        -> inferredFrom
        -> InferredForm inferredFrom derivedGrammar

-- | Fully deconstruct a grammar, producing a primitive grammar suitable for
--   use in ParseGrammarK.
--
--   It works by repeatedly applying DerivedFrom until a fix-point is found.
type family DeconstructGrammar (derivedGrammar :: *) :: * where
    DeconstructGrammar derivedGrammar = DeconstructGrammarFix derivedGrammar (DerivedFrom derivedGrammar)

type family DeconstructGrammarFix (reference :: *) (derivedGrammar :: *) :: * where
    DeconstructGrammarFix derivedGrammar derivedGrammar = derivedGrammar
    DeconstructGrammarFix derivedGrammar derivedGrammar' =
        DeconstructGrammarFix (DerivedFrom derivedGrammar)
                              (DerivedFrom derivedGrammar')

-- | Reconstruct the inferred grammar of a symbolic grammar from the inferred
--   grammar of a *primitive* symbolic grammar, i.e. something that comes
--   out of ParseGrammarK.
type family TransitiveInferredGrammar (symbolic :: *) (inferred :: *) where
    TransitiveInferredGrammar symbolic inferred =
        TransitiveInferredGrammarRec (symbolic)
                                     (DerivedFrom symbolic)
                                     (symbolic)
                                     (DerivedFrom symbolic)
                                     (inferred)

-- | Companion class for TransitiveInferredGrammar.
class ReconstructInferredGrammar (symbolic :: *) (inferred :: *) where
    reconstructInferredGrammar
        :: Proxy symbolic
        -> inferred
        -> TransitiveInferredGrammar symbolic inferred

instance
    ( ReconstructInferredGrammarRec (symbolic) (DerivedFrom symbolic) (symbolic) (DerivedFrom symbolic) (inferred)
    ) => ReconstructInferredGrammar symbolic inferred
  where
    reconstructInferredGrammar symbolic =
        reconstructInferredGrammarRec symbolic derived symbolic derived
      where
        derived :: Proxy (DerivedFrom symbolic)
        derived = Proxy

-- | Reconstruct the inferred grammar of a symbolic grammar from the inferred
--   grammar of a *primitive* symbolic grammar, i.e. something that comes
--   out of ParseGrammarK.
--
--   Observe how this one is used by @TransitiveInferredGrammar.
--
--   The first two parameters of this family, @recursive@ and
--   @recursiveDerived@, serve as memory for use in recurse/close cases.
--   They are the @grammar@ and @derivedFrom@ at the most recent observation of
--   @GClose@, or at the first use of this family (top of the call stack, if
--   you will).
--
--   The second pair of parameters, @grammar@ and @derivedFrom@, must always
--   be such that @derivedFrom ~ DerivedFrom grammar@. This is useful
--   because we hold the convention that we can construct the inferred form
--   of a grammar from the inferred form of the grammar from which it was
--   derived. That second parameter in the pair, @derivedFrom@, also controls
--   recursion in this family: as soon as it becomes a primitive symbolic
--   grammar, we can appeal to InferredFrom.
type family TransitiveInferredGrammarRec (recursive:: *) (recursiveDerived :: *) (grammar :: *) (derivedFrom :: *) (inferred :: *) :: * where

    TransitiveInferredGrammarRec goal r grammar GEmpty PEmpty =
        InferredForm PEmpty grammar

    TransitiveInferredGrammarRec goal r grammar GTrivial PTrivial =
        InferredForm PTrivial grammar

    TransitiveInferredGrammarRec goal r grammar (GSymbol symbol) (PSymbol symbol parameters) =
        InferredForm (PSymbol symbol parameters) grammar

    TransitiveInferredGrammarRec goal r grammar (GProduct left right) (PProduct left' right') =
        InferredForm (PProduct (TransitiveInferredGrammarRec goal r left (DerivedFrom left) left')
                               (TransitiveInferredGrammarRec goal r right (DerivedFrom right) right')
                     )
                     (grammar)

    TransitiveInferredGrammarRec goal r grammar (GSum left right) (PSum ('Left left')) =
        InferredForm (PSum ('Left (TransitiveInferredGrammarRec goal r left (DerivedFrom left) left'))) grammar

    TransitiveInferredGrammarRec goal r grammar (GSum left right) (PSum ('Right right')) =
        InferredForm (PSum ('Right (TransitiveInferredGrammarRec goal r right (DerivedFrom right) right'))) grammar

    -- TBD WHY must we use (DerivedFrom goal) here? It seems, by observation,
    -- to be the right choice, but I cannot reason through it.
    TransitiveInferredGrammarRec goal r grammar GRecurse (PRecurse recurse) =
        InferredForm (PRecurse (TransitiveInferredGrammarRec goal r (DerivedFrom goal) r recurse)) grammar

    -- Notice our choice of new reference parameters: we just copy them from
    -- the second pair of parameters.
    TransitiveInferredGrammarRec goal r grammar (GClose grammar') (PClose grammar'') =
        InferredForm (PClose (TransitiveInferredGrammarRec grammar (GClose grammar') grammar' (DerivedFrom grammar') grammar''))
                     (grammar)

    TransitiveInferredGrammarRec goal r grammar grammar inferred = CouldNotInfer goal r grammar inferred

    -- In this case, we have not reached a primitive form, so all we can do
    -- is recursive through DerivedFrom.
    TransitiveInferredGrammarRec goal r grammar grammar' inferred =
        InferredForm (TransitiveInferredGrammarRec goal r (DerivedFrom grammar) (DerivedFrom grammar') inferred) grammar

-- A type for use in TransitiveInferredGrammar. In case the grammar could not
-- be reconstructed, you get this somewhere in a tree of InferredFrom.
-- The parameter should indicate why the family got stuck.
data CouldNotInfer goal r grammar inferred = CouldNotInfer

-- | Companion class for TransitiveInferredGrammarRec.
class ReconstructInferredGrammarRec (recursive :: *) (recursiveDerived :: *) (grammar :: *) (derivedFrom :: *) (inferred :: *) where
    reconstructInferredGrammarRec
        :: Proxy recursive
        -> Proxy recursiveDerived
        -> Proxy grammar
        -> Proxy derivedFrom
        -> inferred
        -> TransitiveInferredGrammarRec recursive recursiveDerived grammar derivedFrom inferred

--    TransitiveInferredGrammarRec goal r grammar GEmpty PEmpty =
--        InferredForm PEmpty grammar
instance {-# OVERLAPS #-}
    ( InferredGrammar PEmpty grammar
    ) => ReconstructInferredGrammarRec goal r grammar GEmpty PEmpty
  where
    reconstructInferredGrammarRec _ _ grammar _ = inferFromUnderlying grammar

--    TransitiveInferredGrammarRec goal r grammar GTrivial PTrivial =
--        InferredForm PTrivial grammar
instance {-# OVERLAPS #-}
    ( InferredGrammar PTrivial grammar
    ) => ReconstructInferredGrammarRec goal r grammar GTrivial PTrivial
  where
    reconstructInferredGrammarRec _ _ grammar _ = inferFromUnderlying grammar

--    TransitiveInferredGrammarRec goal r grammar (GSymbol symbol) (PSymbol symbol parameters) =
--        InferredForm (PSymbol symbol parameters) grammar
instance {-# OVERLAPS #-}
    ( InferredGrammar (PSymbol symbol parameters) grammar
    ) => ReconstructInferredGrammarRec goal r grammar (GSymbol symbol) (PSymbol symbol parameters)
  where
    reconstructInferredGrammarRec _ _ grammar _ = inferFromUnderlying grammar

--    TransitiveInferredGrammarRec goal r grammar (GProduct left right) (PProduct left' right') =
--        InferredForm (PProduct (TransitiveInferredGrammarRec goal r left (DerivedFrom left) left')
--                               (TransitiveInferredGrammarRec goal r right (DerivedFrom right) right')
--                     )
--                     (grammar)
instance {-# OVERLAPS #-}
    ( ReconstructInferredGrammarRec goal r left (DerivedFrom left) left'
    , ReconstructInferredGrammarRec goal r right (DerivedFrom right) right'
    , InferredGrammar (PProduct (TransitiveInferredGrammarRec goal r left (DerivedFrom left) left')
                                (TransitiveInferredGrammarRec goal r right (DerivedFrom right) right')
                      )
                      (grammar)
    ) => ReconstructInferredGrammarRec goal r grammar (GProduct left right) (PProduct left' right')
  where
    reconstructInferredGrammarRec goal r grammar _ term = case term of
        PProduct left' right' -> inferFromUnderlying grammar (PProduct left'' right'')
          where
            left'' = reconstructInferredGrammarRec goal r (Proxy :: Proxy left) (Proxy :: Proxy (DerivedFrom left)) left'
            right'' = reconstructInferredGrammarRec goal r (Proxy :: Proxy right) (Proxy :: Proxy (DerivedFrom right)) right'

--    TransitiveInferredGrammarRec goal r grammar (GSum left right) (PSum ('Left left')) =
--        InferredForm (PSum ('Left (TransitiveInferredGrammarRec goal r left (DerivedFrom left) left'))) grammar
instance {-# OVERLAPS #-}
    ( ReconstructInferredGrammarRec goal r left (DerivedFrom left) left'
    , InferredGrammar (PSum ('Left (TransitiveInferredGrammarRec goal r left (DerivedFrom left) left'))
                      )
                      (grammar)
    ) => ReconstructInferredGrammarRec goal r grammar (GSum left right) (PSum ('Left left'))
  where
    reconstructInferredGrammarRec goal r grammar _ term = case term of
        PSumLeft left' -> inferFromUnderlying grammar (PSumLeft left'')
          where
            left'' = reconstructInferredGrammarRec goal r (Proxy :: Proxy left) (Proxy :: Proxy (DerivedFrom left)) left'

--    TransitiveInferredGrammarRec goal r grammar (GSum left right) (PSum ('Right right')) =
--        InferredForm (PSum ('Right (TransitiveInferredGrammarRec goal r right (DerivedFrom right) right'))) grammar
instance {-# OVERLAPS #-}
    ( ReconstructInferredGrammarRec goal r right (DerivedFrom right) right'
    , InferredGrammar (PSum ('Right (TransitiveInferredGrammarRec goal r right (DerivedFrom right) right'))
                      )
                      (grammar)
    ) => ReconstructInferredGrammarRec goal r grammar (GSum right right) (PSum ('Right right'))
  where
    reconstructInferredGrammarRec goal r grammar _ term = case term of
        PSumRight right' -> inferFromUnderlying grammar (PSumRight right'')
          where
            right'' = reconstructInferredGrammarRec goal r (Proxy :: Proxy right) (Proxy :: Proxy (DerivedFrom right)) right'


--    TransitiveInferredGrammarRec goal r grammar GRecurse (PRecurse recurse) =
--        InferredForm (PRecurse (TransitiveInferredGrammarRec goal r (DerivedFrom goal) r recurse)) grammar
instance {-# OVERLAPS #-}
    ( ReconstructInferredGrammarRec goal r (DerivedFrom goal) r recurse
    , InferredGrammar (PRecurse (TransitiveInferredGrammarRec goal r (DerivedFrom goal) r recurse)
                      )
                      (grammar)
    ) => ReconstructInferredGrammarRec goal r grammar GRecurse (PRecurse recurse)
  where
    reconstructInferredGrammarRec goal r grammar _ term = case term of
        PRecurse recurse -> inferFromUnderlying grammar (PRecurse recurse')
          where
            recurse' = reconstructInferredGrammarRec goal r (Proxy :: Proxy (DerivedFrom goal)) r recurse

--    TransitiveInferredGrammarRec goal r grammar (GClose grammar') (PClose grammar'') =
--        InferredForm (PClose (TransitiveInferredGrammarRec grammar (GClose grammar') grammar' (DerivedFrom grammar') grammar''))
--                     (grammar)
instance {-# OVERLAPS #-}
    ( ReconstructInferredGrammarRec grammar (GClose grammar') grammar' (DerivedFrom grammar') grammar''
    , InferredGrammar (PClose (TransitiveInferredGrammarRec grammar (GClose grammar') grammar' (DerivedFrom grammar') grammar'')
                      )
                      (grammar)
    ) => ReconstructInferredGrammarRec goal r grammar (GClose grammar') (PClose grammar'')
  where
    reconstructInferredGrammarRec goal r grammar gclose term = case term of
        PClose grammar'' -> inferFromUnderlying grammar (PClose close)
          where
            close = reconstructInferredGrammarRec grammar gclose (Proxy :: Proxy grammar') (Proxy :: Proxy (DerivedFrom grammar')) grammar''

--    TransitiveInferredGrammarRec goal r grammar grammar inferred = CouldNotInfer goal r grammar inferred
{-
 - Removing this one because it causes big overlap problems.
instance {-# OVERLAPS #-}
    (   TransitiveInferredGrammarRec goal r grammar grammar inferred
      ~ CouldNotInfer goal r grammar inferred
    ) => ReconstructInferredGrammarRec goal r grammar grammar inferred 
  where
    reconstructInferredGrammarRec _ _ _ _ _ = CouldNotInfer
-}

--    TransitiveInferredGrammarRec goal r grammar grammar' inferred =
--        InferredForm (TransitiveInferredGrammarRec goal r (DerivedFrom grammar) (DerivedFrom grammar') inferred) grammar
instance {-# OVERLAPS #-}
    ( ReconstructInferredGrammarRec goal r (DerivedFrom grammar) (DerivedFrom grammar') inferred
    , InferredGrammar (TransitiveInferredGrammarRec goal r (DerivedFrom grammar) (DerivedFrom grammar') inferred) grammar
    ,   TransitiveInferredGrammarRec goal r grammar grammar' inferred
      ~ InferredForm (TransitiveInferredGrammarRec goal r (DerivedFrom grammar) (DerivedFrom grammar') inferred) grammar
    ) => ReconstructInferredGrammarRec goal r grammar grammar' inferred
  where
    reconstructInferredGrammarRec goal r grammar grammar' inferred =
        inferFromUnderlying grammar $ reconstructInferredGrammarRec goal r (Proxy :: Proxy (DerivedFrom grammar)) (Proxy :: Proxy (DerivedFrom grammar')) inferred

-- | The empty grammar, which matches nothing.
data GEmpty
newtype PEmpty = PEmpty PEmpty

-- | PEmpty is just Void. It's useful to have something like absurd.
pempty :: PEmpty -> a
pempty (PEmpty t) = pempty t

instance DerivedGrammar GEmpty where
    type DerivedFrom GEmpty = GEmpty

instance
    (
    ) => InferredGrammar PEmpty GEmpty
  where
    type InferredForm PEmpty GEmpty = PEmpty
    inferFromUnderlying _ = id

-- | The trivial grammar, which matches everything.
data GTrivial
data PTrivial = PTrivial

instance DerivedGrammar GTrivial where
    type DerivedFrom GTrivial = GTrivial

instance
    (
    ) => InferredGrammar PTrivial GTrivial
  where
    type InferredForm PTrivial GTrivial = PTrivial
    inferFromUnderlying _ = id

-- | A Symbol, the atomic unit of a grammar.
--   Elements of the list @l@ can be @Check t@, or @Infer@.
--   This will match @ty ps rest@ whenever @ps@ matches @l@. @ps@ must be a list
--   of @P s@. In order to match, the lists must be of the same length, and
--   every @Check t@ in @l@ must have a @P t@ at the same place in @ps@.
data GSymbol (ty :: [*] -> * -> *)
data PSymbol (ty :: [*] -> * -> *) (ps :: [*]) where
    PSymbol :: symbol ps rest -> PSymbol symbol ps

instance DerivedGrammar (GSymbol symbol) where
    type DerivedFrom (GSymbol symbol) = GSymbol symbol

instance
    ( 
    ) => InferredGrammar (PSymbol symbol parameters) (GSymbol symbol)
  where
    type InferredForm (PSymbol symbol parameters) (GSymbol symbol) =
        PSymbol symbol parameters
    inferFromUnderlying _ = id


-- | A conjunction, or sequence, of two grammars.
data GProduct (left :: *) (right :: *)

data PProduct (left :: *) (right :: *) where
    PProduct :: left -> right -> PProduct left right

instance
    ( DerivedGrammar left
    , DerivedGrammar right
    ) => DerivedGrammar (GProduct left right)
  where
    type DerivedFrom (GProduct left right) =
        GProduct (DerivedFrom left) (DerivedFrom right)

instance
    ( DerivedGrammar left
    , DerivedGrammar right
    ) => InferredGrammar (PProduct left' right') (GProduct left right)
  where
    type InferredForm (PProduct left' right') (GProduct left right) =
        PProduct left' right'
    inferFromUnderlying _ = id

-- | A disjunction, or choice, of two grammars.
data GSum (left :: *) (right :: *)
data PSum (t :: Either * *) where
    PSumLeft :: leftGrammar -> PSum ('Left leftGrammar)
    PSumRight :: rightGrammar -> PSum ('Right rightGrammar)

instance
    ( DerivedGrammar left
    , DerivedGrammar right
    ) => DerivedGrammar (GSum left right)
  where
    type DerivedFrom (GSum left right) =
        GSum (DerivedFrom left) (DerivedFrom right)

instance
    ( DerivedGrammar left
    , DerivedGrammar right
    ) => InferredGrammar (PSum ('Left left')) (GSum left right)
  where
    type InferredForm (PSum ('Left left')) (GSum left right) =
        PSum ('Left left')
    inferFromUnderlying _ = id

instance
    ( DerivedGrammar left
    , DerivedGrammar right
    ) => InferredGrammar (PSum ('Right right')) (GSum left right)
  where
    type InferredForm (PSum ('Right right')) (GSum left right) =
        PSum ('Right right')
    inferFromUnderlying _ = id

-- | A type to express recursion in a grammar.
data GRecurse

-- | The type parameter gives the inferred variant of the recursive grammar.
data PRecurse (grammar :: *) where
    PRecurse :: grammar -> PRecurse grammar

instance DerivedGrammar GRecurse where
    type DerivedFrom GRecurse = GRecurse

instance
    (
    ) => InferredGrammar (PRecurse grammar) GRecurse
  where
    -- Here we need the *top* level recursion, the highest derived grammar
    -- against which we're inferring!
    type InferredForm (PRecurse grammar) GRecurse = PRecurse grammar
    inferFromUnderlying _ = id

-- | Close a grammar to recursion.
data GClose t

data PClose (grammar :: *) where
    PClose :: grammar -> PClose grammar

instance
    ( DerivedGrammar grammar
    ) => DerivedGrammar (GClose grammar)
  where
    type DerivedFrom (GClose grammar) = GClose (DerivedFrom grammar)

instance
    ( DerivedGrammar grammar
    ) => InferredGrammar (PClose grammar') (GClose grammar)
  where
    type InferredForm (PClose grammar') (GClose grammar) = PClose grammar'
    inferFromUnderlying _ = id

-- | A derived grammar which sequences 0 or more possibly distinct grammars.
data GAllOf (grammars :: [*])

data PAllOf (inferredGrammars :: [*]) where
    PAllOfNil :: PAllOf '[]
    PAllOfCons :: grammar -> PAllOf grammars -> PAllOf (grammar ': grammars)

-- | A function to extract the grammar list from GAllOf
type family PAllOfGrammars (allOf :: *) :: [*] where
    PAllOfGrammars (PAllOf grammars) = grammars

instance
    (
    ) => DerivedGrammar (GAllOf '[])
  where
    type DerivedFrom (GAllOf '[]) = GTrivial

-- | Observe that we do *not* use DerivedFrom on @grammar@. We merely expand
--   the @GAllOf grammars@ into a @GProduct@ of possibly non-primitive grammars.
--   A repeated application, due to @DerivedFrom (GProduct left right)@, will
--   expand the subgrammars.
instance
    ( DerivedGrammar (GAllOf grammars)
    ) => DerivedGrammar (GAllOf (grammar ': grammars))
  where
    type DerivedFrom (GAllOf (grammar ': grammars)) =
        GProduct grammar (DerivedFrom (GAllOf grammars))

instance
    (
    ) => InferredGrammar PTrivial (GAllOf '[])
  where
    type InferredForm PTrivial (GAllOf '[]) = PAllOf '[]
    inferFromUnderlying _ = const PAllOfNil

-- | The role of this instance is not to infer the subgrammars, but rather to
--   *assume* that they have already been inferred, and roll them up into a
--   @PAllOf grammars@
instance
    ( InferredGrammar right (GAllOf grammars)
    -- This equality is obvious...
    ,   InferredForm right (GAllOf grammars)
      ~ PAllOf (PAllOfGrammars (InferredForm right (GAllOf grammars)))
    ) => InferredGrammar (PProduct left right) (GAllOf (grammar ': grammars))
  where
    type InferredForm (PProduct left right) (GAllOf (grammar ': grammars)) =
        PAllOf (left ': PAllOfGrammars (InferredForm right (GAllOf grammars)))
    inferFromUnderlying _ (PProduct left right) =
        PAllOfCons (left)
                   (inferFromUnderlying (Proxy :: Proxy (GAllOf grammars)) right)

-- | A disjunction of 0 or more grammars.
data GOneOf (grammars :: [*])

-- | The parsed type for GOneOf. Like PSum, it does not contain in its type
--   every grammar from the disjunction. Instead, there is only one, namely
--   the one which was actually parsed. It also carries an index so that we
--   can compute which one of the disjuncts was in fact parsed.
data POneOf (index :: Nat) (inferredGrammar :: *) where
    POneOfHere :: inferredGrammar -> POneOf Z inferredGrammar
    POneOfThere :: POneOf n inferredGrammar -> POneOf (S n) inferredGrammar

type family POneOfGrammar (oneOf :: *) :: * where
    POneOfGrammar (POneOf n grammar) = grammar

type family POneOfIndex (oneOf :: *) :: Nat where
    POneOfIndex (POneOf n grammar) = n

data Nat where
    Z :: Nat
    S :: Nat -> Nat

instance
    (
    ) => DerivedGrammar (GOneOf '[])
  where
    type DerivedFrom (GOneOf '[]) = GEmpty

instance
    ( DerivedGrammar (GOneOf grammars)
    ) => DerivedGrammar (GOneOf (grammar ': grammars))
  where
    type DerivedFrom (GOneOf (grammar ': grammars)) =
        GSum grammar (DerivedFrom (GOneOf grammars))

instance
    (
    ) => InferredGrammar PEmpty (GOneOf '[])
  where
    type InferredForm PEmpty (GOneOf '[]) = POneOf Z PEmpty
    inferFromUnderlying _ = pempty

instance
    ( DerivedGrammar (GOneOf grammars)
    ) => InferredGrammar (PSum ('Left here)) (GOneOf (grammar ': grammars))
  where
    type InferredForm (PSum ('Left here)) (GOneOf (grammar ': grammars)) =
        POneOf Z here
    inferFromUnderlying _ sum = case sum of
        PSumLeft left -> POneOfHere left

instance
    ( InferredGrammar there (GOneOf grammars)
    -- This equality is obviously true.
    ,   InferredForm there (GOneOf grammars)
      ~ POneOf (POneOfIndex (InferredForm there (GOneOf grammars)))
               (POneOfGrammar (InferredForm there (GOneOf grammars)))
    ) => InferredGrammar (PSum ('Right there)) (GOneOf (grammar ': grammars))
  where
    type InferredForm (PSum ('Right there)) (GOneOf (grammar ': grammars)) =
        POneOf (S (POneOfIndex (InferredForm there (GOneOf grammars))))
               (POneOfGrammar (InferredForm there (GOneOf grammars)))
    inferFromUnderlying _ sum = case sum of
        PSumRight right -> POneOfThere (inferFromUnderlying (Proxy :: Proxy (GOneOf grammars)) right)

type Test1 = GAllOf '[GSymbol TestSymbol, GOneOf '[GSymbol TestSymbol, GTrivial]]
type Test1Parsed = GrammarParseInferred (ParseGrammarK (DeconstructGrammar Test1)
                                                       (GrammarMatch (TestSymbol '[] (TestSymbol '[] GEnd)))
                                                       (DeconstructGrammar Test1)
                                        )

-- | 0 or more of a grammar in sequence.
data GMany (grammar :: *)

-- | The inferred type of a @GMany@.
data PMany (grammars :: [*]) where
    PManyNil :: PMany '[]
    PManyCons
        :: inferredGrammar
        -> PMany inferredGrammars
        -> PMany (inferredGrammar ': inferredGrammars)

type family PManyGrammars (pmany :: *) :: [*] where
    PManyGrammars (PMany grammars) = grammars

instance
    ( DerivedGrammar grammar
    ) => DerivedGrammar (GMany grammar)
  where
    type DerivedFrom (GMany grammar) =
        GClose (GOneOf '[GAllOf '[grammar, GRecurse], GTrivial])

instance
    ( DerivedGrammar grammar
    ) => InferredGrammar (PClose (POneOf (S Z) PTrivial)) (GMany grammar)
  where
    type InferredForm (PClose (POneOf (S Z) PTrivial)) (GMany grammar) = PMany '[]
    inferFromUnderlying _ term = case term of
        PClose (POneOfThere (POneOfHere PTrivial)) -> PManyNil

instance
    ( InferredGrammar recurse (GMany grammar')
    -- This equality is obviously true.
    ,   InferredForm recurse (GMany grammar')
      ~ PMany (PManyGrammars (InferredForm recurse (GMany grammar')))
    ) => InferredGrammar (PClose (POneOf Z (PAllOf '[grammar, PRecurse recurse]))) (GMany grammar')
  where
    type InferredForm (PClose (POneOf Z (PAllOf '[grammar, PRecurse recurse]))) (GMany grammar') =
        PMany (grammar ': PManyGrammars (InferredForm recurse (GMany grammar')))
    inferFromUnderlying proxy term = case term of
        PClose (POneOfHere (PAllOfCons here (PAllOfCons (PRecurse recurse) PAllOfNil))) ->
            PManyCons here (inferFromUnderlying (Proxy :: Proxy (GMany grammar')) recurse)

-- | Indicate the end of a sequence of symbols.
--   The sequences which we shall be parsing are composed of * -> * types.
--   They are to be plugged with a GEnd to obtain a *.
data GEnd = GEnd
deriving instance Show GEnd

-- | Used to indicate that we're looking to match a grammar.
--   Compare at @GrammarParse@ and @GrammarNoParse@, which indicate that we have
--   attempted to match a grammar, and succeeded or failed, respectively.
data GrammarMatch t = GrammarMatch {
      getGrammarMatch :: t
    }
deriving instance Show t => Show (GrammarMatch t)

-- | Indicates a parse of @gammar@, with @remainder@ the unparsed tail,
--   relative to @recursion@.
data GrammarParse grammar remainder where
    GrammarParse
        :: grammar
        -> remainder
        -> GrammarParse grammar remainder

-- | Indicates no parse.
data GrammarNoParse = GrammarNoParse

-- | This type family will parse a sequence of symbols to a grammar.
--   - @recursion@ is the reference for recursive grammars.
--   - @ty@ is the type to parse, analagous to a string under a string parser.
--   - @grammar@ is the grammar to parse against, analagous to the target type
--     of a string parser.
type family ParseGrammarK (recursion :: *) (ty :: *) (grammar :: *) :: * where

    -- GTrivial matches anything.
    ParseGrammarK recursion (GrammarMatch anything) (GTrivial) =
        GrammarParse PTrivial anything

    -- GEmpty matches nothing.
    ParseGrammarK recursion (GrammarMatch anything) (GEmpty) =
        GrammarNoParse

    -- GSymbol.
    -- We match the parameters, and feed those into the symbol matching
    -- family. Only if the symbol types are the same, and their parameters
    -- match, do we give a parse.
    ParseGrammarK recursion (GrammarMatch ty) (GSymbol ty') =
        ParseGrammarSymbolK (recursion)
                            (GrammarMatch ty)
                            (GSymbol ty')

    -- GRecurse
    ParseGrammarK recursion anything (GRecurse) =
        ParseGrammarRecurseK recursion anything (GRecurse)

    -- GClose
    ParseGrammarK recursion anything (GClose grammar) =
        ParseGrammarCloseK recursion anything (GClose grammar) 

    -- GProduct
    ParseGrammarK recursion (GrammarMatch ty) (GProduct left right) =
        ParseGrammarProductK (recursion)
                             (GrammarMatch ty)
                             (GProduct left right)
                             ()

    -- GSum
    ParseGrammarK recursion (GrammarMatch ty) (GSum left right) =
        ParseGrammarSumK (recursion)
                         (GrammarMatch ty)
                         (GSum left right)
                         (GrammarMatch ty)

-- | Companion class to ParseGrammarK. Its instances exactly mirror the
--   clauses of that family.
class ParseGrammar (recursion :: *) (ty :: *) (grammar :: *) where
    parseGrammar
        :: Proxy recursion
        -> ty
        -> Proxy grammar
        -> ParseGrammarK recursion ty grammar

instance
    (
    ) => ParseGrammar recursion (GrammarMatch anything) GTrivial
  where
    parseGrammar _ (GrammarMatch anything) _ = GrammarParse PTrivial anything

instance
    (
    ) => ParseGrammar recursion (GrammarMatch anything) GEmpty
  where
    parseGrammar _ _ _ = GrammarNoParse

instance
    ( ParseGrammarSymbol (recursion)
                         (GrammarMatch ty)
                         (GSymbol ty')
    ) => ParseGrammar recursion (GrammarMatch ty) (GSymbol ty')
  where
    parseGrammar recursion ty grammar =
        parseGrammarSymbol recursion ty grammar

instance
    ( ParseGrammarRecurse recursion anything (GRecurse)
    ) => ParseGrammar recursion anything (GRecurse)
  where
    parseGrammar = parseGrammarRecurse

instance
    ( ParseGrammarClose recursion anything (GClose grammar)
    ) => ParseGrammar recursion anything (GClose grammar)
  where
    parseGrammar = parseGrammarClose

instance
    ( ParseGrammarProduct recursion anything (GProduct left right) ()
    ,   ParseGrammarK recursion anything (GProduct left right)
      ~ ParseGrammarProductK recursion anything (GProduct left right) ()
    ) => ParseGrammar recursion anything (GProduct left right)
  where
    parseGrammar recursion anything gproduct =
        parseGrammarProduct recursion anything gproduct ()

instance
    ( ParseGrammarSum recursion anything (GSum left right) anything
    ,   ParseGrammarK recursion anything (GSum left right)
      ~ ParseGrammarSumK recursion anything (GSum left right) anything
    ) => ParseGrammar recursion anything (GSum left right)
  where
    parseGrammar recursion anything sproduct =
        parseGrammarSum recursion anything sproduct anything

type family ParseGrammarSymbolK (recursion :: *) (ty :: *) (grammar :: *) :: * where

    ParseGrammarSymbolK recursion (GrammarMatch (ty ps rest)) (GSymbol ty) =
        GrammarParse (PSymbol ty ps) rest

    ParseGrammarSymbolK recursion (GrammarMatch ty) (GSymbol (ty' :: [*] -> * -> *)) =
        GrammarNoParse

-- | Companion class to ParseGrammarSymbolK.
class ParseGrammarSymbol (recursion :: *) (ty :: *) (grammar :: *) where
    parseGrammarSymbol
        :: Proxy recursion
        -> ty
        -> Proxy grammar
        -> ParseGrammarSymbolK recursion ty grammar

instance {-# OVERLAPS #-}
    ( GrammarSymbol (ty ps)
    ) => ParseGrammarSymbol recursion (GrammarMatch (ty ps rest)) (GSymbol ty)
  where
    parseGrammarSymbol _ (GrammarMatch ty) _ = GrammarParse (PSymbol ty) (splitGrammarSymbol ty)

instance {-# OVERLAPS #-}
    (   ParseGrammarSymbolK recursion (GrammarMatch ty) (GSymbol ty')
      ~ GrammarNoParse
    ) => ParseGrammarSymbol recursion (GrammarMatch ty) (GSymbol ty')
  where
    parseGrammarSymbol _ _ _ = GrammarNoParse

-- | Observe how we treat the parameter to GRecurse.
--   When we parse the input using the recursion reference, we may get a parse,
--   and the parse we get may not be exactly the same as the recursion type,
--   because parameters may be inferred. If the GRecurse parameter is Infer
--   then we take this as it is, otherwise (it's Check) we demand that it
--   matches the expected parameter.
--
--   TODO this needs revision. For the Check case, we just want to ensure that
--   the form of the grammar, not its parameters, remains the same, no?
--   
type family ParseGrammarRecurseK (recursion :: *) (ty :: *) (grammar :: *) :: * where

    ParseGrammarRecurseK recursion (GrammarParse recursive rest) GRecurse =
        GrammarParse (PRecurse recursive) rest

    ParseGrammarRecurseK recursion GrammarNoParse GRecurse = GrammarNoParse

    ParseGrammarRecurseK recursion (GrammarMatch ty) (GRecurse) =
        ParseGrammarRecurseK (recursion)
                             (ParseGrammarK recursion (GrammarMatch ty) recursion)
                             (GRecurse)

-- | Companion class to ParseGrammarRecurseK.
class ParseGrammarRecurse (recursion :: *) (ty :: *) (grammar :: *) where
    parseGrammarRecurse
        :: Proxy recursion
        -> ty
        -> Proxy grammar
        -> ParseGrammarRecurseK recursion ty grammar

instance
    (
    ) => ParseGrammarRecurse recursion (GrammarParse recursive rest) GRecurse
  where
    parseGrammarRecurse _ (GrammarParse this rest) _ = GrammarParse (PRecurse this) rest

instance
    (
    ) => ParseGrammarRecurse recursion GrammarNoParse GRecurse
  where
    parseGrammarRecurse _ grammarNoParse _ = grammarNoParse

instance
    ( ParseGrammarRecurse (recursion)
                          (ParseGrammarK recursion (GrammarMatch ty) recursion)
                          (GRecurse)
    , ParseGrammar recursion (GrammarMatch ty) recursion
    ) => ParseGrammarRecurse recursion (GrammarMatch ty) (GRecurse)
  where
    parseGrammarRecurse recursion (GrammarMatch ty) grecurse =
        parseGrammarRecurse (recursion)
                            (parseGrammar recursion (GrammarMatch ty) recursion)
                            (grecurse)

type family ParseGrammarCloseK (recursion :: *) (ty :: *) (grammar :: *) :: * where

    ParseGrammarCloseK recursion (GrammarParse closed rest) (GClose grammar) =
        GrammarParse (PClose closed) rest

    ParseGrammarCloseK recursion GrammarNoParse (GClose grammar) =
        GrammarNoParse

    -- Called from ParseGrammarK: try to parse with the new recursion reference.
    -- The above two cases will collect the output and in case of a parse,
    -- replace the recursion reference.
    ParseGrammarCloseK recursion (GrammarMatch ty) (GClose grammar) =
        ParseGrammarCloseK (recursion)
                           (ParseGrammarK (GClose grammar) (GrammarMatch ty) grammar)
                           (GClose grammar)

-- | Companion class to ParseGrammarCloseK.
class ParseGrammarClose (recursion :: *) (ty :: *) (grammar :: *) where
    parseGrammarClose
        :: Proxy recursion
        -> ty
        -> Proxy grammar
        -> ParseGrammarCloseK recursion ty grammar

instance
    (
    ) => ParseGrammarClose recursion (GrammarParse close rest) (GClose grammar)
  where
    parseGrammarClose _ (GrammarParse this rest) _ = GrammarParse (PClose this) rest

instance
    (
    ) => ParseGrammarClose recursion GrammarNoParse (GClose grammar)
  where
    parseGrammarClose _ grammarNoParse _ = grammarNoParse

instance
    ( ParseGrammarClose (recursion)
                        (ParseGrammarK (GClose grammar) (GrammarMatch ty) grammar)
                        (GClose grammar)
    , ParseGrammar (GClose grammar) (GrammarMatch ty) grammar
    ) => ParseGrammarClose recursion (GrammarMatch ty) (GClose grammar)
  where
    parseGrammarClose recursion (GrammarMatch ty) gclose =
        parseGrammarClose (recursion)
                          (parseGrammar gclose (GrammarMatch ty) grammar)
                          (gclose)
      where
        grammar :: Proxy grammar
        grammar = Proxy

-- Parsing a product proceeds by trying the left, using its output to try the
-- right, and if either fails, giving GrammarNoParse.
-- Care is taken to ensure that the resulting GrammarParse has the right
-- type, i.e. GProduct left right. For this, we use new types to signal where
-- we are in the process of parsing.
--
-- That last parameter, @leftParse@, is here for the benefit of the companion
-- class, which shall need access to the parsed value of the left term in
-- case the right term parses, in order to construct the full parsed grammar
-- value.
type family ParseGrammarProductK (recursion :: *) (ty :: *) (grammar :: *) (leftParse :: *) :: * where

    -- Here we know it's a recursive call from the final clause of this family.
    -- It means the left was parsed, and @rest@ is the remaining (unparsed)
    -- type, which must parse under right.
    --
    -- NB left' not necessarily left, as parsing can change the type by
    -- inferring parameters.
    ParseGrammarProductK recursion (GrammarParse left' rest) (ParseGrammarProductLeft left right) () =
        ParseGrammarProductK (recursion)
                             (ParseGrammarK recursion (GrammarMatch rest) right)
                             (ParseGrammarProductRight left right)
                             (GrammarParse left' rest)

    ParseGrammarProductK recursion (GrammarParse right' rest) (ParseGrammarProductRight left right) (GrammarParse left' rest') =
        GrammarParse (PProduct left' right') rest

    -- Here we know it's a recursive call from the final clause of this family.
    -- It means the left failed to parse, so the whole thing fails.
    ParseGrammarProductK recursion (GrammarNoParse) (ParseGrammarProductLeft left right) () =
        GrammarNoParse

    ParseGrammarProductK recursion (GrammarNoParse) (ParseGrammarProductRight left right) (GrammarParse left' rest') =
        GrammarNoParse

    -- Try parsing to left, and pass its output back to this family.
    ParseGrammarProductK recursion (GrammarMatch ty) (GProduct left right) () =
        ParseGrammarProductK (recursion)
                             (ParseGrammarK recursion (GrammarMatch ty) left)
                             (ParseGrammarProductLeft left right)
                             ()

data ParseGrammarProductLeft left right
data ParseGrammarProductRight left right

-- | Companion class to ParseGrammarProductK.
class ParseGrammarProduct (recursion :: *) (ty :: *) (grammar :: *) (leftParse :: *) where
    parseGrammarProduct
        :: Proxy recursion
        -> ty
        -> Proxy grammar
        -> leftParse
        -> ParseGrammarProductK recursion ty grammar leftParse

instance
    ( ParseGrammarProduct (recursion)
                          (ParseGrammarK recursion (GrammarMatch rest) right)
                          (ParseGrammarProductRight left right)
                          (GrammarParse left' rest)
    , ParseGrammar recursion (GrammarMatch rest) right
    ) => ParseGrammarProduct recursion (GrammarParse left' rest) (ParseGrammarProductLeft left right) ()
  where
    parseGrammarProduct recursion (GrammarParse this rest) _ () =
        parseGrammarProduct (recursion)
                            (parseGrammar recursion (GrammarMatch rest) (Proxy :: Proxy right))
                            (Proxy :: Proxy (ParseGrammarProductRight left right))
                            (GrammarParse this rest)

-- This is the instance which demands that fourth parameter. Observe how we
-- use it to create the product grammar.
instance
    (
    ) => ParseGrammarProduct recursion (GrammarParse right' rest) (ParseGrammarProductRight left right) (GrammarParse left' rest')
  where
    parseGrammarProduct _ (GrammarParse right rest) _ (GrammarParse left rest') =
        GrammarParse (PProduct left right) rest

instance
    (
    ) => ParseGrammarProduct recursion GrammarNoParse (ParseGrammarProductLeft left right) ()
  where
    parseGrammarProduct _ grammarNoParse _ _ = grammarNoParse

instance
    (
    ) => ParseGrammarProduct recursion GrammarNoParse (ParseGrammarProductRight left right) (GrammarParse left' rest')
  where
    parseGrammarProduct _ grammarNoParse _ _ = grammarNoParse

instance
    ( ParseGrammarProduct (recursion)
                          (ParseGrammarK recursion (GrammarMatch ty) left)
                          (ParseGrammarProductLeft left right)
                          ()
    , ParseGrammar recursion (GrammarMatch ty) left
    ) => ParseGrammarProduct recursion (GrammarMatch ty) (GProduct left right) ()
  where
    parseGrammarProduct recursion (GrammarMatch ty) gproduct () =
        parseGrammarProduct (recursion)
                            (parseGrammar recursion (GrammarMatch ty) (Proxy :: Proxy left))
                            (Proxy :: Proxy (ParseGrammarProductLeft left right))
                            ()

-- Like for ParseGrammarProductK, we use special types to signal the parsing
-- process. Here, we also have a fourth parameter, for the benefit of the
-- companion class. It shall contain the initial thing which was to be parsed,
-- so we can feed it to right in case left fails.
--
type family ParseGrammarSumK (recursion :: *) (ty :: *) (grammar :: *) (initial :: *) :: * where

    -- The left parsed; we're done.
    ParseGrammarSumK recursion (GrammarParse left' rest) (ParseGrammarSumLeft left right) initial =
        GrammarParse (PSum ('Left left')) rest

    -- The right parsed; we're done.
    ParseGrammarSumK recursion (GrammarParse right' rest) (ParseGrammarSumRight left right) initial =
        GrammarParse (PSum ('Right right')) rest

    -- The left failed to parse; try the right.
    ParseGrammarSumK recursion (GrammarNoParse) (ParseGrammarSumLeft left right) initial =
        ParseGrammarSumK (recursion)
                         (ParseGrammarK recursion initial right)
                         (ParseGrammarSumRight left right)
                         (initial)

    -- The right failed to parse; that's it, we're done.
    ParseGrammarSumK recursion (GrammarNoParse) (ParseGrammarSumRight left right) initial =
        GrammarNoParse

    ParseGrammarSumK recursion (GrammarMatch ty) (GSum left right) (GrammarMatch ty) =
        ParseGrammarSumK (recursion)
                         (ParseGrammarK recursion (GrammarMatch ty) left)
                         (ParseGrammarSumLeft left right)
                         (GrammarMatch ty)

data ParseGrammarSumLeft (left :: *) (right :: *)
data ParseGrammarSumRight (left :: *) (right :: *)

-- | Companion class to ParseGrammarSumK.
class ParseGrammarSum (recursion :: *) (ty :: *) (grammar :: *) (initial :: *) where
    parseGrammarSum
        :: Proxy recursion
        -> ty
        -> Proxy grammar
        -> initial
        -> ParseGrammarSumK recursion ty grammar initial

instance
    (
    ) => ParseGrammarSum recursion (GrammarParse left' rest) (ParseGrammarSumLeft left right) initial
  where
    parseGrammarSum _ (GrammarParse this rest) _ _ =
        GrammarParse (PSumLeft this) rest

instance
    (
    ) => ParseGrammarSum recursion (GrammarParse right' rest) (ParseGrammarSumRight left right) initial
  where
    parseGrammarSum _ (GrammarParse this rest) _ _ =
        GrammarParse (PSumRight this) rest

instance
    ( ParseGrammarSum (recursion)
                      (ParseGrammarK recursion initial right)
                      (ParseGrammarSumRight left right)
                      (initial)
    , ParseGrammar recursion initial right
    ) => ParseGrammarSum recursion GrammarNoParse (ParseGrammarSumLeft left right) initial
  where
    parseGrammarSum recursion _ _ initial =
       parseGrammarSum (recursion)
                       (parseGrammar recursion initial (Proxy :: Proxy right))
                       (Proxy :: Proxy (ParseGrammarSumRight left right))
                       (initial)

instance
    (
    ) => ParseGrammarSum recursion GrammarNoParse (ParseGrammarSumRight left right) initial
  where
    parseGrammarSum _ grammarNoParse _ _ = grammarNoParse

instance
    ( ParseGrammarSum (recursion)
                      (ParseGrammarK recursion (GrammarMatch ty) left)
                      (ParseGrammarSumLeft left right)
                      (GrammarMatch ty)
    , ParseGrammar recursion (GrammarMatch ty) left
    ) => ParseGrammarSum recursion (GrammarMatch ty) (GSum left right) (GrammarMatch ty)
  where
    parseGrammarSum recursion grammarMatch gsum initial =
        parseGrammarSum (recursion)
                        (parseGrammar recursion grammarMatch (Proxy :: Proxy left))
                        (Proxy :: Proxy (ParseGrammarSumLeft left right))
                        (initial)

-- This will print a sequence of symbols without constructing a Grammar value.
-- The @m@ parameter will be used as a spacer, between every two symbols.
class PrintGrammarSymbols symbols m where
    printGrammarSymbols :: m -> symbols -> m

instance {-# OVERLAPS #-}
    ( PrintGrammarSymbol symbol m
    ) => PrintGrammarSymbols (symbol GEnd) m
  where
    printGrammarSymbols _ = printGrammarSymbol (Proxy :: Proxy m)

instance {-# OVERLAPS #-}
    ( PrintGrammarSymbol symbol m
    , PrintGrammarSymbols symbols m
    , Monoid m
    ) => PrintGrammarSymbols (symbol symbols) m
  where
    printGrammarSymbols spacer term =
        let symbols = splitGrammarSymbol term
            proxyM :: Proxy m
            proxyM = Proxy
        in  mconcat [
                  printGrammarSymbol proxyM term
                , spacer
                , printGrammarSymbols spacer symbols
                ]
