{-|
Module      : Data.Type.Grammar
Description : Type-level parsing.
Copyright   : (c) Alexander Vieth, 2015
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)

DEPRECATED this is here for historical reasons. Compared to Data.Type.Parse
it's really cumbersome and also incredibly slow. BUT it's still got some
pretty interesting stuff.

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

import Data.Proxy

import Debug.Trace

data Symbol1 (ps :: [*]) (t :: *) where
    Symbol1 :: t -> Symbol1 '[] t
instance GrammarSymbol (Symbol1 '[]) where
    splitGrammarSymbol (Symbol1 t) = t
data Symbol2 (ps :: [*]) (t :: *) where
    Symbol2 :: t -> Symbol2 '[] t
instance GrammarSymbol (Symbol2 '[]) where
    splitGrammarSymbol (Symbol2 t) = t

{-
GrammarParse q _ _ _ = parseGrammarV (Symbol1 GEnd) (Proxy :: Proxy (DeconstructGrammar (GMany (GSymbol Symbol1))))
GrammarParse r _ _ _ = parseGrammarV (Symbol1 (Symbol1 GEnd)) (Proxy :: Proxy (DeconstructGrammar (GMany (GSymbol Symbol1))))
GrammarParse s _ _ _ = parseGrammarV (Symbol1 (Symbol1 (Symbol1 GEnd))) (Proxy :: Proxy (DeconstructGrammar (GMany (GSymbol Symbol1))))
GrammarParse t _ _ _ = parseGrammarV (Symbol1 (Symbol1 (Symbol1 (Symbol1 GEnd)))) (Proxy :: Proxy (DeconstructGrammar (GMany (GSymbol Symbol1))))
-}
--GrammarParse q _ _ _ = parseDerivedGrammar ((Symbol1 (Symbol1 (Symbol1 (Symbol1 (Symbol1 (Symbol1 GEnd))))))) (Proxy :: Proxy (GMany (GSymbol Symbol1)))
--GrammarParse q _ _ _ = parseDerivedGrammar (Symbol1 (Symbol1 GEnd)) (Proxy :: Proxy (GMany (GSymbol Symbol1)))

-- | TBD use an existing Nat implementation? It's so lightweight though, may
--   not even be worth the extra package dependency (currently we depend only
--   upon base).
data Nat where
    Z :: Nat
    S :: Nat -> Nat

type family NatSum (x :: Nat) (y :: Nat) :: Nat where
    NatSum Z n = n
    NatSum (S n) m = S (NatSum n m)

type family DropSymbols (count :: Nat) (sym :: *) :: * where
    DropSymbols Z any = any
    DropSymbols (S n) (ty (ps :: [*]) rest) = DropSymbols n rest

-- | Use this type in the parameter list for a Symbol.
data P (t :: k) :: *

-- | Anything which can be used as a symbol in a grammar. This class shows how
--   to pop it off and obtain the tail of the sequence. It's analagous to
--   a Stream typeclass which may be demanded of the input stream for a typical
--   term parser.
class GrammarSymbol (ty :: * -> *) where
    splitGrammarSymbol :: ty rest -> rest

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
--   Notice the relationship between this family and @DerivedFrom@.
--   This one is essentially responsible for lifting @DerivedFrom@ into a
--   recursive action.
type family DeconstructGrammar (derivedGrammar :: *) :: * where
    DeconstructGrammar GEmpty = GEmpty
    DeconstructGrammar GTrivial = GTrivial
    DeconstructGrammar (GSymbol symbol) = GSymbol symbol
    DeconstructGrammar (GProduct left right) =
        GProduct (DeconstructGrammar left) (DeconstructGrammar right)
    DeconstructGrammar (GSum left right) =
        GSum (DeconstructGrammar left) (DeconstructGrammar right)
    DeconstructGrammar GRecurse = GRecurse
    DeconstructGrammar (GClose close) = GClose (DeconstructGrammar close)
    DeconstructGrammar (GOpen open) = GOpen (DeconstructGrammar open)
    DeconstructGrammar derived = DeconstructGrammar (DerivedFrom derived)

-- We have the derived grammars and their inferred forms (call them higher
-- inferred forms), and we have the primitive grammars and their inferred
-- forms (primitive inferred forms). It is taken for granted that a higher
-- inferred form can be produced from the inferred form of the grammar from
-- which its grammar is derived. This relationship is witnessed by the
-- InferredGrammar class.
--
-- Suppose we have in hand the complete derivation of a derived grammar, i.e.
-- a list of types, '[ d_1, .., d_n ] such that DerivedFrom d_k = d_{k+1}
-- and where d_n is a primitive grammar.
--
-- We want to compute not only the higher inferred form, but every intermediate
-- type necessary in order to direct the selection of InferredGrammar instances
-- which give rise to the value for that higher inferred form.
-- The crucial point: instance constraints for reconstruction must *NOT*
-- contain potentially large type family applications.
-- The only way I see fit to do this is by building a derivation *tree*; a
-- list will not do.
--
-- Yes, what we require is a derivation tree.
-- For a derived grammar, record every DerivedFrom until a primitive form is
-- reached. If it is one of the 5 recursive forms, place a derivation tree in
-- its parameter(s). The head of each list will therefore be a primitive form.
-- To reconstruct, inspect the head of the list. If it's a primitive form,
-- reconstruct its children (against the inferred primitive form that we have
-- in hand! because presumably we have just parsed a primitive grammar!).
-- If it's not a primitive form, use inferFromUnderlying on the current inferred
-- form against the current symbolic grammar in the list to get the next
-- inferred form. Yeah... So from the derivation tree the ultimate inferred
-- form is determined? Seems so. But will it be computed efficiently?

-- | TODO Confusing terminology. This means a *shallow* primitive, so that
--   a GProduct left right is primitive even if left and right are not
--   primitive.
type family IsPrimitive (grammar :: *) :: Bool where
    IsPrimitive GEmpty = 'True
    IsPrimitive GTrivial = 'True
    IsPrimitive (GSymbol sym) = 'True
    IsPrimitive GRecurse = 'True
    IsPrimitive (GClose closed) = 'True
    IsPrimitive (GOpen opened) = 'True
    IsPrimitive (GProduct left right) = 'True
    IsPrimitive (GSum left right) = 'True
    IsPrimitive nonPrimitive = 'False

-- The 8 primitive symbolic grammars, differing only in that the recursive
-- symbol, DRecurse, has a parameter. They are for use in the derivation
-- tree.
data DEmpty
data DTrivial
data DSymbol sym
data DProduct left right
data DSum left right
data DRecurse recurse
data DClose close
data DOpen open

-- | Call with @primitiveInferred@ as the inferred output of a successful
--   parse of a primitive grammar via @ParseGrammarK@. @grammar@ is any
--   derived symbolic grammar.
--
--   TODO describe in great detail the form of the derivation tree.
--
--   TBD need to handle a recursion stack here? When we reach a GRecurse,
--   we must be careful to infer against top of stack.
--   Hm, but perhaps that needn't be in the type family, but only in the
--   class.
--   So from the GrammarDerivationTree and the recursion stack types, can we
--   come up with a term of type
--   @GrammarDerivationTreeInferredForm derivationTree@?
-- 
type family GrammarDerivationTree (recursionStack :: [*]) (grammar :: *) (primitiveInferred :: *) :: [(*, *)] where
    GrammarDerivationTree recursionStack grammar primitiveInferred =
        GrammarDerivationTree2 (IsPrimitive grammar) recursionStack grammar primitiveInferred

-- An invariant that we must keep: for every element of derivation tree (list
-- of tuples) we have that the first one is a symbolic grammar type and
-- the second is its associated inferred form. 
type family GrammarDerivationTree2 (isPrimitive :: Bool) (recursionStack :: [*]) (grammar :: *) (primitiveInferred :: *) :: [(*, *)] where

    GrammarDerivationTree2 'True recursionStack GEmpty PEmpty = '[ '(DEmpty, PEmpty) ]

    GrammarDerivationTree2 'True recursionStack GTrivial PTrivial = '[ '(DTrivial, PTrivial) ]

    GrammarDerivationTree2 'True recursionStack (GSymbol sym) (PSymbol sym ps) = '[ '(DSymbol sym, PSymbol sym ps) ]

    GrammarDerivationTree2 'True (top ': stack) GRecurse (PRecurse recurse) = 
        GrammarDerivationTreeRecurse (GrammarDerivationTree (top ': stack) top recurse)

    GrammarDerivationTree2 'True recursionStack (GClose closed) (PClose closed') =
        GrammarDerivationTreeClose (GrammarDerivationTree (GClose closed ': recursionStack) closed closed')

    GrammarDerivationTree2 'True (top ': stack) (GOpen opened) (POpen opened') =
        GrammarDerivationTreeOpen (GrammarDerivationTree stack opened opened')

    GrammarDerivationTree2 'True recursionStack (GProduct left right) (PProduct count left' right') =
        GrammarDerivationTreeProduct count
                                     (GrammarDerivationTree recursionStack left left')
                                     (GrammarDerivationTree recursionStack right right')

    -- NB we ditch the unused branch, anticipating a performance win.
    GrammarDerivationTree2 'True recursionStack (GSum left right) (PSum ('Left left')) =
        GrammarDerivationTreeSumLeft (GrammarDerivationTree recursionStack left left')

    GrammarDerivationTree2 'True recursionStack (GSum left right) (PSum ('Right right')) =
        GrammarDerivationTreeSumRight (GrammarDerivationTree recursionStack right right')

    -- A non-primitive grammar type. We compute the derivation tree for
    -- the grammar from which it's derived and then place it at the front of
    -- the list via GrammarDerivationTreeCons, which uses InferredForm.
    GrammarDerivationTree2 'False recursionStack grammar primitiveInferred =
        GrammarDerivationTreeCons grammar (GrammarDerivationTree recursionStack (DerivedFrom grammar) primitiveInferred)

type family GrammarDerivationTreeRecurse (derivationTree :: [(*, *)]) :: [(*, *)] where
    GrammarDerivationTreeRecurse derivationTree = '[ '(
          DRecurse derivationTree
        , PRecurse (GrammarDerivationTreeInferredForm derivationTree)
        )]

type family GrammarDerivationTreeClose (derivationTree :: [(*, *)]) :: [(*, *)] where
    GrammarDerivationTreeClose derivationTree = '[ '(
          DClose derivationTree
        , PClose (GrammarDerivationTreeInferredForm derivationTree)
        )]

type family GrammarDerivationTreeOpen (derivationTree :: [(*, *)]) :: [(*, *)] where
    GrammarDerivationTreeOpen derivationTree = '[ '(
          DOpen derivationTree
        , POpen (GrammarDerivationTreeInferredForm derivationTree)
        )]

type family GrammarDerivationTreeProduct (count :: Nat) (derivationTreeLeft :: [(*, *)]) (derivationTreeRight :: [(*, *)]) :: [(*, *)] where
    GrammarDerivationTreeProduct count left right = '[ '(
          DProduct left right
        , PProduct count (GrammarDerivationTreeInferredForm left) (GrammarDerivationTreeInferredForm right)
        )]

type family GrammarDerivationTreeSumLeft (derivationTree :: [(*, *)]) :: [(*, *)] where
    GrammarDerivationTreeSumLeft derivationTree = '[ '(
          DSum derivationTree SummandRemoved
        , PSum ('Left (GrammarDerivationTreeInferredForm derivationTree))
        )]

type family GrammarDerivationTreeSumRight (derivationTree :: [(*, *)]) :: [(*, *)] where
    GrammarDerivationTreeSumRight derivationTree = '[ '(
          DSum SummandRemoved derivationTree
        , PSum ('Right (GrammarDerivationTreeInferredForm derivationTree))
        )]

-- | To cons a new entry in a derivation tree, we must exploit @InferredForm@,
--   using the inferred form of the head of the tail.
type family GrammarDerivationTreeCons (grammar :: *) (tail :: [(*, *)]) :: [(*, *)] where
    -- NB: @symbolic ~ DerivedFrom grammar@ by construction (if we've done
    -- anything right!).
    GrammarDerivationTreeCons grammar ( '(symbolic, inferred) ': rest ) =
        '(grammar, InferredForm inferred grammar) ': '(symbolic, inferred) ': rest

-- | A type to indicate that a summand of a symbolic grammar is removed from
--   a derivation tree because it is irrelevant; the other branch was
--   chosen by the parser.
data SummandRemoved

-- | Get the highest-level inferred form from a derivation tree. That's the
--   second component of the head of the list.
--   Relies upon the assumption that @derivationTree@ was produced by
--   @GrammarDerivationTree@.
type family GrammarDerivationTreeInferredForm (derivationTree :: [(*, *)]) :: * where
    GrammarDerivationTreeInferredForm ( '(symbolic, inferred) ': rest ) = inferred

-- | A companion class for @GrammarDerivationTree@. @outcome@, in practice,
--   shall be
--
--     @GrammarDerivationTreeInferredForm derivationTree@
--
--   whenever
--
--     @derivationTree = GrammarDerivationTree '[grammar] grammar primitiveInferred@
--
class ReconstructGrammarK (derivationTree :: [(*, *)]) (primitiveInferred :: *) (outcome :: *) where
    reconstructGrammarK
        :: Proxy derivationTree
        -> primitiveInferred
        -> outcome

instance
    (
    ) => ReconstructGrammarK '[ '(DEmpty, PEmpty) ] PEmpty PEmpty
  where
    reconstructGrammarK _ = id

instance
    (
    ) => ReconstructGrammarK '[ '(DTrivial, PTrivial) ] PTrivial PTrivial
  where
    reconstructGrammarK _ = id

instance
    (
    ) => ReconstructGrammarK '[ '(DSymbol sym, PSymbol sym ps) ] (PSymbol sym ps) (PSymbol sym ps)
  where
    reconstructGrammarK _ = id

instance
    ( ReconstructGrammarK recurse recurse' recurse''
    ) => ReconstructGrammarK '[ '(DRecurse recurse, PRecurse recurse'') ] (PRecurse recurse') (PRecurse recurse'')
  where
    reconstructGrammarK _ (PRecurse recurse') =
        PRecurse reconstructed
      where
        recurse :: Proxy recurse
        recurse = Proxy
        reconstructed :: recurse''
        reconstructed = reconstructGrammarK recurse recurse'

instance
    ( ReconstructGrammarK closed closed' closed''
    ) => ReconstructGrammarK '[ '(DClose closed, PClose closed'') ] (PClose closed') (PClose closed'')
  where
    reconstructGrammarK _ (PClose closed') =
        PClose reconstructed
      where
        closed :: Proxy closed
        closed = Proxy
        reconstructed :: closed''
        reconstructed = reconstructGrammarK closed closed'

instance
    ( ReconstructGrammarK opened opened' opened''
    ) => ReconstructGrammarK '[ '(DOpen opened, POpen opened'') ] (POpen opened') (POpen opened'')
  where
    reconstructGrammarK _ (POpen opened') =
        POpen reconstructed
      where
        opened :: Proxy opened
        opened = Proxy
        reconstructed :: opened''
        reconstructed = reconstructGrammarK opened opened'

instance
    ( ReconstructGrammarK left left' left''
    , ReconstructGrammarK right right' right''
    ) => ReconstructGrammarK '[ '(DProduct left right, PProduct count left'' right'') ] (PProduct count left' right') (PProduct count left'' right'')
  where
    reconstructGrammarK _ (PProduct count left' right') =
        PProduct count left'' right''
      where
        left :: Proxy left
        left = Proxy
        right :: Proxy right
        right = Proxy
        left'' :: left''
        left'' = reconstructGrammarK left left'
        right'' :: right''
        right'' = reconstructGrammarK right right'

instance
    ( ReconstructGrammarK left left' left''
    ) => ReconstructGrammarK '[ '(DSum left SummandRemoved, PSum ('Left left'')) ] (PSum ('Left left')) (PSum ('Left left''))
  where
    reconstructGrammarK _ (PSumLeft left') =
        PSumLeft left''
      where
        left :: Proxy left
        left = Proxy
        left'' :: left''
        left'' = reconstructGrammarK left left'

instance
    ( ReconstructGrammarK right right' right''
    ) => ReconstructGrammarK '[ '(DSum SummandRemoved right, PSum ('Right right'')) ] (PSum ('Right right')) (PSum ('Right right''))
  where
    reconstructGrammarK _ (PSumRight right') =
        PSumRight right''
      where
        right :: Proxy right
        right = Proxy
        right'' :: right''
        right'' = reconstructGrammarK right right'

-- Use of the double-cons pattern prevents overlap, I believe.
instance
    ( GrammarDerivationTreeInferredForm (the ': rest) ~ underlyingInferred
    , InferredForm underlyingInferred grammar ~ inferred
    , InferredGrammar underlyingInferred grammar
    , ReconstructGrammarK (the ': rest) primitiveInferred underlyingInferred
    ) => ReconstructGrammarK ( '(grammar, inferred) ': the ': rest ) primitiveInferred inferred
  where
    reconstructGrammarK _ primitiveInferred =
        inferFromUnderlying grammar reconstructed
      where
        grammar :: Proxy grammar
        grammar = Proxy
        theRest :: Proxy (the ': rest)
        theRest = Proxy
        reconstructed :: underlyingInferred
        reconstructed = reconstructGrammarK theRest primitiveInferred


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
data GProduct (left :: k) (right :: l)

--{-# INLINE grammarProductLeft #-}
grammarProductLeft :: Proxy (GProduct left right) -> Proxy left
grammarProductLeft _ = Proxy

--{-# INLINE grammarProductRight #-}
grammarProductRight :: Proxy (GProduct left right) -> Proxy right
grammarProductRight _ = Proxy

data PProduct (count :: Nat) (left :: *) (right :: *) where
    PProduct :: Proxy count -> left -> right -> PProduct count left right

instance
    (
    ) => DerivedGrammar (GProduct left right)
  where
    type DerivedFrom (GProduct left right) = GProduct left right

instance
    (
    ) => InferredGrammar (PProduct count left' right') (GProduct left right)
  where
    type InferredForm (PProduct count left' right') (GProduct left right) =
        PProduct count left' right'
    inferFromUnderlying _ = id

-- | A disjunction, or choice, of two grammars.
data GSum (left :: k) (right :: l)

data PSum (t :: Either * *) where
    PSumLeft :: leftGrammar -> PSum ('Left leftGrammar)
    PSumRight :: rightGrammar -> PSum ('Right rightGrammar)

instance
    (
    ) => DerivedGrammar (GSum left right)
  where
    type DerivedFrom (GSum left right) = GSum left right

instance
    (
    ) => InferredGrammar (PSum ('Left left')) (GSum left right)
  where
    type InferredForm (PSum ('Left left')) (GSum left right) =
        PSum ('Left left')
    inferFromUnderlying _ = id

instance
    (
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

-- | Close a grammar to recursion. Think of it as pushing onto the recursion
--   stack; this grammar will see itself as the top of the stack.
--   See also GOpen.
data GClose (grammar :: k)

data PClose (grammar :: *) where
    PClose :: grammar -> PClose grammar

instance
    (
    ) => DerivedGrammar (GClose grammar)
  where
    type DerivedFrom (GClose grammar) = GClose grammar

instance
    (
    ) => InferredGrammar (PClose grammar') (GClose grammar)
  where
    type InferredForm (PClose grammar') (GClose grammar) = PClose grammar'
    inferFromUnderlying _ = id

-- | Open a grammar to recursion. Think of it as popping the recursion stack;
--   @grammar@ will see the current recursion stack without its top item.
data GOpen (grammar :: k)

data POpen (inferred :: *) where
    POpen :: inferred -> POpen inferred

instance
    (
    ) => DerivedGrammar (GOpen grammar)
  where
    type DerivedFrom (GOpen grammar) = GOpen grammar

instance
    (
    ) => InferredGrammar (POpen inferred) (GOpen grammar)
  where
    type InferredForm (POpen inferred) (GOpen grammar) = POpen inferred
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
    (
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
    ) => InferredGrammar (PProduct count left right) (GAllOf (grammar ': grammars))
  where
    type InferredForm (PProduct count left right) (GAllOf (grammar ': grammars)) =
        PAllOf (left ': PAllOfGrammars (InferredForm right (GAllOf grammars)))
    inferFromUnderlying _ (PProduct _ left right) =
        PAllOfCons (left)
                   (inferFromUnderlying (Proxy :: Proxy (GAllOf grammars)) right)

-- | A disjunction of 0 or more grammars.
data GOneOf (grammars :: [*])

-- | The parsed type for GOneOf. Like PSum, it does not contain in its type
--   every grammar from the disjunction. Instead, there is only one, namely
--   the one which was actually parsed. It also carries an index so that we
--   can compute which one of the disjuncts was in fact parsed.
data POneOf (index :: Nat) (inferredGrammar :: *) where
    POneOfHere :: inferredGrammar -> POneOf 'Z inferredGrammar
    POneOfThere :: POneOf n inferredGrammar -> POneOf ('S n) inferredGrammar

type family POneOfGrammar (oneOf :: *) :: * where
    POneOfGrammar (POneOf n grammar) = grammar

type family POneOfIndex (oneOf :: *) :: Nat where
    POneOfIndex (POneOf n grammar) = n

pOneOfValue :: POneOf index anything -> anything
pOneOfValue term = case term of
    POneOfHere x -> x
    POneOfThere rest -> pOneOfValue rest

instance
    (
    ) => DerivedGrammar (GOneOf '[])
  where
    type DerivedFrom (GOneOf '[]) = GEmpty

instance
    (
    ) => DerivedGrammar (GOneOf (grammar ': grammars))
  where
    type DerivedFrom (GOneOf (grammar ': grammars)) =
        GSum grammar (DerivedFrom (GOneOf grammars))

instance
    (
    ) => InferredGrammar PEmpty (GOneOf '[])
  where
    type InferredForm PEmpty (GOneOf '[]) = POneOf 'Z PEmpty
    inferFromUnderlying _ = pempty

instance
    (
    ) => InferredGrammar (PSum ('Left here)) (GOneOf (grammar ': grammars))
  where
    type InferredForm (PSum ('Left here)) (GOneOf (grammar ': grammars)) =
        POneOf 'Z here
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
        POneOf ('S (POneOfIndex (InferredForm there (GOneOf grammars))))
               (POneOfGrammar (InferredForm there (GOneOf grammars)))
    inferFromUnderlying _ sum = case sum of
        PSumRight right -> POneOfThere (inferFromUnderlying (Proxy :: Proxy (GOneOf grammars)) right)

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

-- | Note the use of GOpen in the derived form. This is very important!
--   Without it, any grammar with a free GRecurse (one which does not appear
--   under some GClose) would be captured and the meaning of the grammar would
--   change.
instance
    (
    ) => DerivedGrammar (GMany grammar)
  where
    type DerivedFrom (GMany grammar) =
        GClose (GOneOf '[GAllOf '[GOpen grammar, GRecurse], GTrivial])

instance
    (
    ) => InferredGrammar (PClose (POneOf ('S 'Z) PTrivial)) (GMany grammar)
  where
    type InferredForm (PClose (POneOf ('S 'Z) PTrivial)) (GMany grammar) = PMany '[]
    inferFromUnderlying _ term = case term of
        PClose (POneOfThere (POneOfHere PTrivial)) -> PManyNil

instance
    ( InferredForm recurse (GMany grammar') ~ PMany (PManyGrammars (InferredForm recurse (GMany grammar')))
    -- This is obvious: PMany (PManyGrammars x) = x always
    , InferredGrammar recurse (GMany grammar')
    ) => InferredGrammar (PClose (POneOf 'Z (PAllOf '[POpen grammar, PRecurse recurse]))) (GMany grammar')
  where
    type InferredForm (PClose (POneOf 'Z (PAllOf '[POpen grammar, PRecurse recurse]))) (GMany grammar') =
        PMany (grammar ': PManyGrammars (InferredForm recurse (GMany grammar')))
    inferFromUnderlying gmany term = case term of
        PClose (POneOfHere (PAllOfCons (POpen here) (PAllOfCons (PRecurse recurse) PAllOfNil))) ->
            PManyCons here (inferFromUnderlying gmany recurse)

-- | At least 1 occurrence of a grammar in sequence.
data GMany1 (grammar :: *)

-- TODO with GHC 8.0 I believe we will be able to use NonEmpty * here...
-- Or maybe we can even do that now?
data PMany1 (inferred :: *) (inferreds :: [*]) where
    PMany1 :: inferred -> PMany inferreds -> PMany1 inferred inferreds

instance
    (
    ) => DerivedGrammar (GMany1 grammar)
  where
    type DerivedFrom (GMany1 grammar) = GProduct grammar (GMany grammar)

instance
    (
    ) => InferredGrammar (PProduct count inferred (PMany inferreds)) (GMany1 grammar)
  where
    type InferredForm (PProduct count inferred (PMany inferreds)) (GMany1 grammar) =
        PMany1 inferred inferreds
    inferFromUnderlying _ term = case term of
        PProduct _ inferred pmany -> PMany1 inferred pmany

-- | Separate a grammar by another grammar.
data GSepBy (grammar :: *) (grammarSep :: *)

data PSepBy (grammars :: [*]) (grammarSeps :: [*]) where
    PSepByOne :: grammar -> PSepBy '[grammar] '[]
    PSepByMore
        :: grammar
        -> grammarSep
        -> PSepBy grammars grammarSeps
        -> PSepBy (grammar ': grammars) (grammarSep ': grammarSeps)

type family PSepByGrammars (psepby :: *) :: [*] where
    PSepByGrammars (PSepBy grammars grammarSeps) = grammars

type family PSepBySeparators (psepby :: *) :: [*] where
    PSepBySeparators (PSepBy grammars grammarSeps) = grammarSeps

instance
    (
    ) => DerivedGrammar (GSepBy grammar grammarSep)
  where
    type DerivedFrom (GSepBy grammar grammarSep) =
        GAllOf '[grammar, GMany (GAllOf '[grammarSep, grammar])]

instance
    (
    ) => InferredGrammar (PAllOf '[inferred, PMany '[]]) (GSepBy grammar grammarSep)
  where
    type InferredForm (PAllOf '[inferred, PMany '[]]) (GSepBy grammar grammarSep) =
        PSepBy '[inferred] '[]
    inferFromUnderlying _ term = case term of
        PAllOfCons inferred _ -> PSepByOne inferred

instance
    ( InferredGrammar (PAllOf '[inferred', PMany rest]) (GSepBy grammar grammarSep)
    -- This is a clear fact about PSepBy and its relation to PSepByGrammars,
    -- PSepBySeparators
    ,   PSepBy (PSepByGrammars (InferredForm (PAllOf '[inferred', PMany rest]) (GSepBy grammar grammarSep)))
               (PSepBySeparators (InferredForm (PAllOf '[inferred', PMany rest]) (GSepBy grammar grammarSep)))
      ~ InferredForm (PAllOf '[inferred', PMany rest]) (GSepBy grammar grammarSep)
    ) => InferredGrammar (PAllOf '[inferred, PMany ((PAllOf '[inferredSep, inferred']) ': rest)]) (GSepBy grammar grammarSep)
  where
    type InferredForm (PAllOf '[inferred, PMany ((PAllOf '[inferredSep, inferred']) ': rest)]) (GSepBy grammar grammarSep) =
        PSepBy (inferred ': PSepByGrammars (InferredForm (PAllOf '[inferred', PMany rest]) (GSepBy grammar grammarSep)))
               (inferredSep ': PSepBySeparators (InferredForm (PAllOf '[inferred', PMany rest]) (GSepBy grammar grammarSep)))
    inferFromUnderlying gproxy term = case term of
        PAllOfCons inferred
            (PAllOfCons
            (PManyCons
            (PAllOfCons inferredSep
            (PAllOfCons inferred' _))
            rest) _) -> PSepByMore inferred
                                   inferredSep
                                   (inferFromUnderlying gproxy (PAllOfCons inferred' (PAllOfCons rest PAllOfNil)))


-- | An optional grammar.
data GOptional (grammar :: *)

data POptional (maybeGrammar :: Maybe *) where
    POptionalJust :: grammar -> POptional ('Just grammar)
    POptionalNothing :: POptional 'Nothing

instance
    (
    ) => DerivedGrammar (GOptional grammar)
  where
    type DerivedFrom (GOptional grammar) = GOneOf '[grammar, GTrivial]

instance
    (
    ) => InferredGrammar (POneOf 'Z inferred) (GOptional grammar)
  where
    type InferredForm (POneOf 'Z inferred) (GOptional grammar) = POptional ('Just inferred)
    inferFromUnderlying _ term = case term of
        POneOfHere inferred -> POptionalJust inferred

instance
    (
    ) => InferredGrammar (POneOf ('S 'Z) PTrivial) (GOptional grammar)
  where
    type InferredForm (POneOf ('S 'Z) PTrivial) (GOptional grammar) = POptional 'Nothing
    inferFromUnderlying _ _ = POptionalNothing

-- | Indicate the end of a sequence of symbols.
--   The sequences which we shall be parsing are composed of * -> * types.
--   They are to be plugged with a GEnd to obtain a *.
data GEnd = GEnd
deriving instance Show GEnd

-- | Used to indicate that we're looking to match a grammar.
--   Compare at @GrammarParse@ and @GrammarNoParse@, which indicate that we have
--   attempted to match a grammar, and succeeded or failed, respectively.
data GrammarMatch t where
    GrammarMatch :: GrammarMatchC term => term -> GrammarMatch term

class GrammarMatchC (term :: *) where
    type GrammarMatchT term :: *
    grammarMatchSplit :: term -> GrammarMatchT term

instance {-# OVERLAPS #-} GrammarSymbol sym => GrammarMatchC (sym t) where
    type GrammarMatchT (sym t) = t
    grammarMatchSplit = splitGrammarSymbol

instance {-# OVERLAPS #-} GrammarMatchC GEnd where
    type GrammarMatchT GEnd = GEnd
    grammarMatchSplit = id

-- | @inferred@ was parsed from @input@ using @count@ symbols, leaving
--   @remainder@ symbols unparsed.
data GrammarParse (inferred :: *) (count :: Nat) (input :: *) (remainder :: *) where
    GrammarParse
        :: inferred
        -> Proxy count
        -> input
        -> remainder
        -> GrammarParse inferred count input remainder

{-# INLINE grammarParseRemainder #-}
grammarParseRemainder :: GrammarParse inferred count input remainder -> remainder
grammarParseRemainder (GrammarParse _ _ _ remainder) = remainder

{-# INLINE grammarParseInferred #-}
grammarParseInferred :: GrammarParse inferred count input remainder -> inferred
grammarParseInferred (GrammarParse inferred _ _ _) = inferred

-- | Indicates no parse.
data GrammarNoParse = GrammarNoParse

type family GrammarSymbolMatches (sym :: *) (grammar :: *) :: Bool where
    GrammarSymbolMatches (GrammarMatch (ty ps rest)) (GSymbol ty) = 'True
    GrammarSymbolMatches (GrammarMatch ty) (GSymbol ty') = 'False

{-# NOINLINE grammarSymbolMatches #-}
grammarSymbolMatches :: sym -> Proxy grammar -> Proxy (GrammarSymbolMatches sym grammar)
grammarSymbolMatches _ _ = Proxy

-- | This type family will parse a sequence of symbols against a grammar.
--
--   The output is either @GrammarNoParse@, or @GrammarParse inferred rest@,
--   where @inferred@ is a singleton type which, for products and sums, carries
--   extra information indicating, respectively, the number of symbols taken
--   by the first grammar, and the variant which was parsed.
--
--   Parameters are
--   - @recursion@ is the "call stack", needed for recursive grammars.
--   - @ty@ is the type to parse, analagous to a string under a string parser.
--   - @grammar@ is the grammar to parse against, analagous to the target type
--     of a string parser.
--
type family ParseGrammarK (ty :: *) (grammar :: *) (recursion :: [*]) :: * where

    -- GTrivial matches anything.
    ParseGrammarK (GrammarMatch anything) (GTrivial) recursion =
        GrammarParse PTrivial Z anything anything

    -- GEmpty matches nothing.
    ParseGrammarK (GrammarMatch anything) (GEmpty) recursion =
        GrammarNoParse

    -- GSymbol.
    -- We match the parameters, and feed those into the symbol matching
    -- family. Only if the symbol types are the same, and their parameters
    -- match, do we give a parse.
    ParseGrammarK (GrammarMatch ty) (GSymbol ty') recursion =
        ParseGrammarSymbolK (GrammarMatch ty)
                            (GSymbol ty')
                            (GrammarSymbolMatches (GrammarMatch ty) (GSymbol ty'))
                            (recursion)

    -- GRecurse
    ParseGrammarK (GrammarMatch anything) (GRecurse) recursion =
        ParseGrammarRecurseK (GrammarMatch anything) (GRecurse) recursion

    -- GClose
    ParseGrammarK (GrammarMatch anything) (GClose grammar) recursion =
        ParseGrammarCloseK (GrammarMatch anything) (GClose grammar) recursion

    -- GOpen
    ParseGrammarK (GrammarMatch anything) (GOpen grammar) recursion =
        ParseGrammarOpenK (GrammarMatch anything) (GOpen grammar) recursion

    -- GProduct
    ParseGrammarK (GrammarMatch ty) (GProduct left right) recursion =
        ParseGrammarProductK (GrammarMatch ty)
                             (GProduct left right)
                             ()
                             recursion

    -- GSum
    ParseGrammarK (GrammarMatch ty) (GSum left right) recursion =
        ParseGrammarSumK (GrammarMatch ty)
                         (GSum left right)
                         (GrammarMatch ty)
                         (recursion)

type family ParseGrammarSymbolK (ty :: *) (grammar :: *) (matches :: Bool) (recursion :: [*]) :: * where

    ParseGrammarSymbolK (GrammarMatch (ty ps rest)) (GSymbol ty) 'True recursion =
        GrammarParse (PSymbol ty ps) (S Z) (ty ps rest) rest

    ParseGrammarSymbolK (GrammarMatch ty) (GSymbol (ty' :: [*] -> * -> *)) 'False recursion =
        GrammarNoParse

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
type family ParseGrammarRecurseK (ty :: *) (grammar :: *) (recursion :: [*]) :: * where

    ParseGrammarRecurseK (GrammarParse recursive count input rest) GRecurse recursion =
        GrammarParse (PRecurse recursive) count input rest

    ParseGrammarRecurseK GrammarNoParse GRecurse recursion = GrammarNoParse

    ParseGrammarRecurseK (GrammarMatch ty) (GRecurse) (top ': rest) =
        ParseGrammarRecurseK (ParseGrammarK (GrammarMatch ty) top (top ': rest))
                             (GRecurse)
                             (top ': rest)

type family ParseGrammarOpenK (ty :: *) (grammar :: *) (recursion :: [*]) :: * where

    ParseGrammarOpenK (GrammarParse opened count input rest) (GOpen grammar) recursion =
        GrammarParse (POpen opened) count input rest

    ParseGrammarOpenK GrammarNoParse (GOpen grammar) recursion =
        GrammarNoParse

    ParseGrammarOpenK (GrammarMatch ty) (GOpen grammar) (top ': bottom) =
        ParseGrammarOpenK (ParseGrammarK (GrammarMatch ty) grammar bottom)
                          (GOpen grammar)
                          (top ': bottom)

type family ParseGrammarCloseK (ty :: *) (grammar :: *) (recursion :: [*]) :: * where

    ParseGrammarCloseK (GrammarParse closed count input rest) (GClose grammar) recursion =
        GrammarParse (PClose closed) count input rest

    ParseGrammarCloseK GrammarNoParse (GClose grammar) recursion =
        GrammarNoParse

    -- Called from ParseGrammarK: try to parse with the new recursion reference.
    -- The above two cases will collect the output and in case of a parse,
    -- replace the recursion reference.
    ParseGrammarCloseK (GrammarMatch ty) (GClose grammar) recursion =
        ParseGrammarCloseK (ParseGrammarK (GrammarMatch ty) grammar (GClose grammar ': recursion))
                           (GClose grammar)
                           recursion

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
type family ParseGrammarProductK (ty :: *) (grammar :: *) (leftParse :: *) (recursion :: [*]) :: * where

    -- Here we know it's a recursive call from the final clause of this family.
    -- It means the left was parsed, and @rest@ is the remaining (unparsed)
    -- type, which must parse under right.
    --
    -- NB left' not necessarily left, as parsing can change the type by
    -- inferring parameters.
    ParseGrammarProductK (GrammarParse left' count input rest) (ParseGrammarProductLeft left right) () recursion =
        ParseGrammarProductK (ParseGrammarK (GrammarMatch rest) right recursion)
                             (ParseGrammarProductRight left right)
                             (GrammarParse left' count input rest)
                             recursion

    ParseGrammarProductK (GrammarParse right' count input rest) (ParseGrammarProductRight left right) (GrammarParse left' count' input' rest') recursion =
        -- Be skeptical of the choice of parameters.
        -- We sum the counts, because that's the total number of symbols
        -- consumed, but we choose count' for the PProduct output, because
        -- that must be the number of symbols consumed by the *left* grammar.
        -- input' is chosen as the input, because that's the *original* input
        -- for the *whole* product, and rest is chosen because it's the
        -- remainder for the *whole* product parse.
        GrammarParse (PProduct count' left' right') (NatSum count count') input' rest

    -- Here we know it's a recursive call from the final clause of this family.
    -- It means the left failed to parse, so the whole thing fails.
    ParseGrammarProductK (GrammarNoParse) (ParseGrammarProductLeft left right) () recursion =
        GrammarNoParse

    ParseGrammarProductK (GrammarNoParse) (ParseGrammarProductRight left right) (GrammarParse left' count input rest) recursion =
        GrammarNoParse

    -- Try parsing to left, and pass its output back to this family.
    ParseGrammarProductK (GrammarMatch ty) (GProduct left right) () recursion =
        ParseGrammarProductK (ParseGrammarK (GrammarMatch ty) left recursion)
                             (ParseGrammarProductLeft left right)
                             ()
                             recursion

data ParseGrammarProductLeft left right
data ParseGrammarProductRight left right

{-# NOINLINE parseGrammarProductLeft #-}
parseGrammarProductLeft :: Proxy (GProduct left right) -> Proxy (ParseGrammarProductLeft left right)
parseGrammarProductLeft _ = Proxy

{-# NOINLINE parseGrammarProductRight #-}
parseGrammarProductRight :: Proxy (ParseGrammarProductLeft left right) -> Proxy (ParseGrammarProductRight left right)
parseGrammarProductRight _ = Proxy

{-# NOINLINE parseGrammarProductRightGrammar #-}
parseGrammarProductRightGrammar :: Proxy (ParseGrammarProductLeft left right) -> Proxy right
parseGrammarProductRightGrammar _ = Proxy

-- Like for ParseGrammarProductK, we use special types to signal the parsing
-- process. Here, we also have a fourth parameter, for the benefit of the
-- companion class. It shall contain the initial thing which was to be parsed,
-- so we can feed it to right in case left fails.
--
type family ParseGrammarSumK (ty :: *) (grammar :: *) (initial :: *) (recursion :: [*]) :: * where

    -- The left parsed; we're done.
    ParseGrammarSumK (GrammarParse left' count input rest) (ParseGrammarSumLeft left right) initial recursion =
        GrammarParse (PSum ('Left left')) count input rest

    -- The right parsed; we're done.
    ParseGrammarSumK (GrammarParse right' count input rest) (ParseGrammarSumRight left right) initial recursion =
        GrammarParse (PSum ('Right right')) count input rest

    -- The left failed to parse; try the right.
    ParseGrammarSumK (GrammarNoParse) (ParseGrammarSumLeft left right) initial recursion =
        ParseGrammarSumK (ParseGrammarK initial right recursion)
                         (ParseGrammarSumRight left right)
                         (initial)
                         recursion

    -- The right failed to parse; that's it, we're done.
    ParseGrammarSumK (GrammarNoParse) (ParseGrammarSumRight left right) initial recursion =
        GrammarNoParse

    ParseGrammarSumK (GrammarMatch ty) (GSum left right) (GrammarMatch ty) recursion =
        ParseGrammarSumK (ParseGrammarK (GrammarMatch ty) left recursion)
                         (ParseGrammarSumLeft left right)
                         (GrammarMatch ty)
                         recursion

data ParseGrammarSumLeft (left :: *) (right :: *)
data ParseGrammarSumRight (left :: *) (right :: *)

-- ULTIMATELY what we want is some function
--
--   parseGrammar
--       :: Proxy recursion
--       -> ty
--       -> Proxy grammar
--       -> ParseGrammarK recursion ty grammar
--
-- and we wish to compute ParseGrammarK only once.
--
-- With the type in hand, we should be able to get away with only traversing
-- it, rather than recomputing it for product/sum cases. We just need to grab
-- the associated symbol data constructors. If we have in hand the input symbol
-- sequence, as well as the grammar type, we can analyze both of them jointly.
--
-- How will we proceed with products? Evidently, the class ParseGrammarR
-- must produce the remainder so it can feed to the next one.

-- | NB we aim to compute ParseGrammarK as few times as possible, i.e. at most
--   once. That's why we state the variable @parsed@ and give an equality.
--   GHC may complain that it's redundant, but it's not!!
--
--   Would be cool if GHC did not create the coercion between parsed
--   and the PareGrammarK term, but rather, replaced every occurrence of
--   parsed with the RHS. Does that happen? If not, why not?
parseGrammarV
    :: forall term grammar parsed .
       ( ParseGrammarR term parsed
       , parsed ~ ParseGrammarK (GrammarMatch term) grammar '[grammar]
       )
    => term
    -> Proxy grammar
    -> parsed
parseGrammarV term proxyGrammar = parseGrammarR term (Proxy :: Proxy parsed)

-- TODO almost there! We just have to factor the reconstruction through the
-- GrammarParse/GrammarNoParse kind-of-functor-like-notion.
-- How best to do this, though? New type families and classes which wrap/unwrap
-- is the only thing that comes to mind...

data GrammarInferred

type family GrammarDerivationTreeThruParse (recursionStack :: [*]) (derivedGrammar :: *) (parsed :: *) where
    GrammarDerivationTreeThruParse recursionStack derivedGrammar GrammarNoParse = GrammarNoParse
    GrammarDerivationTreeThruParse recursionStack derivedGrammar (GrammarParse inferred count ty rest) =
        GrammarParse (Proxy (GrammarDerivationTree recursionStack derivedGrammar inferred)) count ty rest

type family GrammarDerivationTreeInferredFormThruParse (derivationTreeThruParse :: *) :: * where
    GrammarDerivationTreeInferredFormThruParse GrammarNoParse = GrammarNoParse
    GrammarDerivationTreeInferredFormThruParse (GrammarParse (Proxy derivationTree) count ty rest) =
        GrammarParse (GrammarDerivationTreeInferredForm derivationTree) count ty rest

type family GrammarDerivationTreeThruParseRetract (derivationTreeThruParse :: *) :: [(*, *)] where
    GrammarDerivationTreeThruParseRetract (GrammarParse (Proxy derivationTree) count ty rest) = derivationTree

class ReconstructGrammarThruParseK derivationTree parsed reconstructed where
    reconstructGrammarThruParseK
        :: Proxy derivationTree
        -> parsed
        -> reconstructed

instance
    (
    ) => ReconstructGrammarThruParseK derivationTree GrammarNoParse GrammarNoParse
  where
    reconstructGrammarThruParseK _ = id

instance
    ( ReconstructGrammarK derivationTree parsed inferred
    ) => ReconstructGrammarThruParseK derivationTree (GrammarParse parsed count ty rest) (GrammarParse inferred count ty rest)
  where
    reconstructGrammarThruParseK derivationTree (GrammarParse parsed count ty rest) =
        GrammarParse (reconstructGrammarK derivationTree parsed) count ty rest

parseDerivedGrammar
    :: forall derivedGrammar term grammar deconstructed reconstructed parsed derivationTree derivationTreeThruParse .
       ( deconstructed ~ DeconstructGrammar derivedGrammar
       , parsed ~ ParseGrammarK (GrammarMatch term) deconstructed '[deconstructed]
       , ParseGrammarR term parsed
       , derivationTreeThruParse ~ GrammarDerivationTreeThruParse '[derivedGrammar] derivedGrammar parsed
       --, reconstructed ~ GrammarDerivationTreeInferredFormThruParse derivationTreeThruParse
       --, derivationTree ~ GrammarDerivationTreeThruParseRetract derivationTreeThruParse
       --, ReconstructGrammarThruParseK derivationTree parsed reconstructed
       )
    => term
    -> Proxy derivedGrammar
    -> reconstructed
parseDerivedGrammar = undefined
{-
parseDerivedGrammar term proxyDerivedGrammar =
    let parsed = parseGrammarR term (Proxy :: Proxy parsed)
        derivationTree :: Proxy derivationTree
        derivationTree = Proxy
    in  reconstructGrammarThruParseK derivationTree parsed
-}

-- | This class discriminates between parse and no parse.
class ParseGrammarR (ty :: *) (parsed :: *) where
    parseGrammarR :: ty -> Proxy parsed -> parsed

instance ParseGrammarR ty GrammarNoParse where
    parseGrammarR _ _ = GrammarNoParse

instance
    ( ParseGrammarQ ty inferred rest
    ) => ParseGrammarR ty (GrammarParse inferred count ty rest)
  where
    parseGrammarR ty _ = GrammarParse inferred Proxy ty rest
      where
        (inferred, rest) = parseGrammarQ ty (Proxy :: Proxy inferred) (Proxy :: Proxy rest)

class ParseGrammarQ (ty :: *) (inferred :: *) (rest :: *) where
    parseGrammarQ :: ty -> Proxy inferred -> Proxy rest -> (inferred, rest)

instance
    (
    ) => ParseGrammarQ ty PTrivial ty
  where
    parseGrammarQ ty _ _ = (PTrivial, ty)

instance
    ( GrammarSymbol (ty ps)
    ) => ParseGrammarQ (ty ps rest) (PSymbol ty ps) rest
  where
    parseGrammarQ sym _ _ = (PSymbol sym, splitGrammarSymbol sym)

instance
    ( ParseGrammarQ ty recurse rest
    ) => ParseGrammarQ ty (PRecurse recurse) rest
  where 
    parseGrammarQ ty _ proxyRest = (PRecurse recurse, rest)
      where
        (recurse, rest) = parseGrammarQ ty (Proxy :: Proxy recurse) proxyRest

instance
    ( ParseGrammarQ ty close rest
    ) => ParseGrammarQ ty (PClose close) rest
  where
    parseGrammarQ ty _ proxyRest = (PClose close, rest)
      where
        (close, rest) = parseGrammarQ ty (Proxy :: Proxy close) proxyRest

instance
    ( ParseGrammarQ ty open rest
    ) => ParseGrammarQ ty (POpen open) rest
  where
    parseGrammarQ ty _ proxyRest = (POpen open, rest)
      where
        (open, rest) = parseGrammarQ ty (Proxy :: Proxy open) proxyRest

instance
    ( tail ~ DropSymbols count ty
    , ParseGrammarQ ty left tail
    , ParseGrammarQ tail right rest
    ) => ParseGrammarQ ty (PProduct count left right) rest
  where
    parseGrammarQ ty _ proxyRest = (PProduct Proxy left right, rest)
      where
        (left, tail) = parseGrammarQ ty (Proxy :: Proxy left) proxyTail
        (right, rest) = parseGrammarQ tail (Proxy :: Proxy right) proxyRest
        proxyTail :: Proxy tail
        proxyTail = Proxy

instance
    ( ParseGrammarQ ty left rest
    ) => ParseGrammarQ ty (PSum ('Left left)) rest
  where 
    parseGrammarQ ty _ proxyRest = (PSumLeft left, rest)
      where
        (left, rest) = parseGrammarQ ty (Proxy :: Proxy left) proxyRest

instance
    ( ParseGrammarQ ty right rest
    ) => ParseGrammarQ ty (PSum ('Right right)) rest
  where 
    parseGrammarQ ty _ proxyRest = (PSumRight right, rest)
      where
        (right, rest) = parseGrammarQ ty (Proxy :: Proxy right) proxyRest

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
