{-|
Module      : Data.Type.Grammar.Precedence
Description : Definition of operator precedence grammar types.
Copyright   : (c) Alexander Vieth, 2015
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE AutoDeriveTypeable #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

--module Data.Type.Grammar.Precedence where

import Data.Proxy
import Data.Type.Grammar

-- Types to describe associativity of infix operators: left-, right-, or non.

-- | 0 or more left-associative infix operators. The elements are tuples because
--   left-associative infix operators can have postfixes. For instance, the
--   SQL JOIN constructions are left-associative, but also come with postfixes
--   like ON or USING.
--   The first component is the infix grammar, second is the postfix. Set
--   the postfix to GTrivial if there's no postfix.
data Infixl (grammars :: [(*, *)])

-- | 0 or more right-associative infix operators. Like Infixl, we take tuples.
--   The reasoning is the same, but here the *prefix* is the *first* element
--   and the infix is the second element.
data Infixr (grammars :: [(*, *)])

-- | 0 or more non-associative infix operators. Unlike left- and right-
--   associative infix operators, these can have a prefix *and* a postfix.
--   They are in the natural order, with the infix operator in the middle.
data Infix (grammars :: [(*, *, *)])

-- To handle infix grammars we use a method in which each precedence level
-- induces a new grammar, which refers to the recursive case: the grammar
-- with all of the higher-precedence operators. The base case is the
-- terminal grammar, or anything between parens.
-- For example, addition and multiplication, with the latter binding tighter,
-- would decompose to something like this:
--
--     A = B{+B}
--     B = C{*C}
--     C = Number | (A)
--
-- where {x} means 0 or more occurrences of x.

-- | First parameter, @operators@, is a list of precedence levels. Each element
--   of the list must be @Infixl grammars@, @Infixr grammars@, or
--   @Infix grammars@, where the @grammars@ parameter is a list of symbolic
--   grammars of infix operators. Thus each precedence level is either left-,
--   right-, or non-associative (you can't mix different associativities of the
--   same precedence).
data GInfix (operators :: [*]) (base :: *) (leftParen :: *) (rightParen :: *)

-- Wish to make the derived grammar and inferred grammar instances just once,
-- for GInfix, eliminating GInfixOpen from the question.
-- To do this, we shall need
--
--   - A type family to compute the derived grammar, iterating over the
--     operators list.
--   - A type family to compute the inferred form
--   - A companion class to give inferFromUnderlying.

type family GInfixDerivedFrom' (ginfix :: *) :: * where
    GInfixDerivedFrom' (GInfix operators base leftParen rightParen) =
        GInfixDerivedFrom operators base leftParen rightParen

type family GInfixDerivedFrom (operators :: [*]) (base :: *) (leftParen :: *) (rightParen :: *) :: * where
    GInfixDerivedFrom operators base leftParen rightParen = GClose (GInfixDerivedFromOpen operators base leftParen rightParen)

type family GInfixDerivedFromOpen (operators :: [*]) (base :: *) (leftParen :: *) (rightParen :: *) :: * where
    GInfixDerivedFromOpen '[] base leftParen rightParen = GInfixDerivedFromOpenBase base leftParen rightParen
    GInfixDerivedFromOpen (operator ': operators) base leftParen rightParen =
        GInfixDerivedFromOpenOperator operator operators base leftParen rightParen

type family GInfixDerivedFromOpenBase (base :: *) (leftParen :: *) (rightParen :: *) :: * where
    GInfixDerivedFromOpenBase base leftParen rightParen = 
        GSum base (GAllOf '[leftParen, GRecurse, rightParen])

type family GInfixDerivedFromOpenOperator (operator :: *) (operators :: [*]) (base :: *) (leftParen :: *) (rightParen :: *) :: * where
    GInfixDerivedFromOpenOperator (Infix infixes) operators base leftParen rightParen =
        GInfixDerivedFromOpenInfix infixes operators base leftParen rightParen
    GInfixDerivedFromOpenOperator (Infixl infixes) operators base leftParen rightParen =
        GInfixDerivedFromOpenInfixl infixes operators base leftParen rightParen
    GInfixDerivedFromOpenOperator (Infixr infixes) operators base leftParen rightParen =
        GInfixDerivedFromOpenInfixr infixes operators base leftParen rightParen

type family GInfixDerivedFromOpenInfix (infixes :: [(*, *, *)]) (operators :: [*]) (base :: *) (leftParen :: *) (rightParen :: *) :: * where
    GInfixDerivedFromOpenInfix '[] operators base leftParen rightParen =
        GInfixDerivedFromOpen operators base leftParen rightParen
    GInfixDerivedFromOpenInfix ( '(pre, inf, post) ': infixes ) operators base leftParen rightParen =
        GSum (GAllOf '[pre, GInfixDerivedFromOpen operators base leftParen rightParen, inf, GInfixDerivedFromOpen operators base leftParen rightParen, post])
             (GInfixDerivedFromOpenInfix infixes operators base leftParen rightParen)

type family GInfixDerivedFromOpenInfixl (infixes :: [(*, *)]) (operators :: [*]) (base :: *) (leftParen :: *) (rightParen :: *) :: * where
    GInfixDerivedFromOpenInfixl infixlGrammars operators base leftParen rightParen =
        GProduct (GInfixDerivedFromOpen operators base leftParen rightParen)
                 (GMany (GOneOf (InfixlGrammar infixlGrammars (GInfixDerivedFromOpen operators base leftParen rightParen))))

-- Derived grammar for left-infix operators.
-- We give something alongs the lines of this, if it means anything:
--
--   A = B { G1 B Q1 | ... | GN B QN }
--
-- where B is the recursive case (GInfixOpen grammars base leftParen rightParen)
-- (containing grammars for all tighter-binding operators), 1,..,N are the
-- grammars in this Infixl level, G is the infix, Q is the postfix.
--
-- Informally: B, followed by 0 or more B's infixed and postfixed by the
-- grammars from the infix definition. See why a left-associative operator
-- can't have a prefix?
type family InfixlGrammar (grammars :: [(*, *)]) (rec :: *) :: [*] where
    InfixlGrammar '[] rec = '[]
    InfixlGrammar ( '(g, p) ': gs) rec = GAllOf '[g, rec, p] ': InfixlGrammar gs rec

type family GInfixDerivedFromOpenInfixr (infixes :: [(*, *)]) (operators :: [*]) (base :: *) (leftParen :: *) (rightParen :: *) :: * where
    GInfixDerivedFromOpenInfixr infixrGrammars operators base leftParen rightParen =
        GProduct (GMany (GOneOf (InfixrGrammar infixrGrammars (GInfixDerivedFromOpen operators base leftParen rightParen))))
                 (GInfixDerivedFromOpen operators base leftParen rightParen)

-- Derived grammar for right-infix operators.
-- We give something alongs the lines of this, if it means anything:
--
--   A = { P1 B G1 | ... | PN B GN } B
--
-- where B is the recursive case (GInfixOpen grammarss base leftParen rightParen)
-- (containing grammars for all tighter-binding operators) and 1,..,N are the
-- grammars in this Infixr level, with P meaning prefix and G meaning infix.
-- Informally: 0 or more B's prefixed and infixed by the grammars from the
-- infixr definition, followed by a B.
type family InfixrGrammar (grammars :: [(*, *)]) (rec :: *) :: [*] where
    InfixrGrammar '[] rec = '[]
    InfixrGrammar ( '(p, g) ': gs) rec = GAllOf '[p, rec, g] ': InfixlGrammar gs rec

-- | GInfix is given in terms of GInfixOpen, so named because it relies upon
--   a free occurrence of GRecurse in the grammar from which it is derived.
instance DerivedGrammar (GInfix operators base leftParen rightParen) where
    type DerivedFrom (GInfix operators base leftParen rightParen) =
        --GInfixDerivedFrom operators base leftParen rightParen
        GClose (GInfixOpen operators operators base leftParen rightParen)

instance
    (
    ) => InferredGrammar (PClose term) (GInfix operators base leftParen rightParen)
  where
    type InferredForm (PClose term) (GInfix operators base leftParen rightParen) =
        term
    inferFromUnderlying _ (PClose term) = term

data GInfixOpen (operators :: [*]) (operatorsRec :: [*]) (base :: *) (leftParen :: *) (rightParen :: *)

data InfixBase (base :: *)
data InfixOperator (pre :: *) (left :: *) (operator :: *) (right :: *) (post :: *)

-- | The inferred form of a GInfixOpen. It's the expression tree.
data PInfix (inferred :: *) where
    PInfixBase
        :: inferred
        -> PInfix (InfixBase inferred)
    PInfixOperator
        :: pre
        -> left
        -> op
        -> right
        -> post
        -> PInfix (InfixOperator pre left op right post)

-- Derived grammar for 0 infix operators.
instance DerivedGrammar (GInfixOpen operators '[] base leftParen rightParen) where
    type DerivedFrom (GInfixOpen operators '[] base leftParen rightParen) =
        GSum base (GAllOf '[leftParen, GRecurse, rightParen])

-- Inferred grammar for 0 infix operators.
instance InferredGrammar (PSum ('Left inferredBase)) (GInfixOpen operators '[] base leftParen rightParen) where
    type InferredForm (PSum ('Left inferredBase)) (GInfixOpen operators '[] base leftParen rightParen) =
        PInfix (InfixBase inferredBase)
    inferFromUnderlying _ term = case term of
        PSumLeft inferredBase -> PInfixBase inferredBase

instance
    ( InferredGrammar recurse (GInfix operators base leftParen rightParen)
    ) => InferredGrammar (PSum ('Right (PAllOf '[inferredLeftParen, PRecurse recurse, inferredRightParen]))) (GInfixOpen operators '[] base leftParen rightParen)
  where
    type InferredForm (PSum ('Right (PAllOf '[inferredLeftParen, PRecurse recurse, inferredRightParen]))) (GInfixOpen operators '[] base leftParen rightParen) =
        InferredForm recurse (GInfix operators base leftParen rightParen)
    inferFromUnderlying proxy term = case term of
        PSumRight (PAllOfCons proxy (PAllOfCons (PRecurse recurse) _)) ->
            inferFromUnderlying (Proxy :: Proxy (GInfix operators base leftParen rightParen)) recurse

-- Derived grammar for infix operators.
-- We give something alongs the lines of this, if it means anything:
--
--   A = [ P1 B G1 B Q1 | ... | PN B GN B QN ] | B
--
-- where B is the recursive case GInfixOpen grammarss base leftParen rightParen
-- (containing grammars for all tighter-binding operators) and 1,..,N are the
-- grammars in this Infix level (PN is prefix, GN infix, QN postfix).
-- Informally: B, or 2 B's interleaved with the infix operator stuff.
instance
    ( DerivedGrammar (GInfixOpen operators grammars base leftParen rightParen)
    ) => DerivedGrammar (GInfixOpen operators (Infix '[] ': grammars) base leftParen rightParen)
  where
    type DerivedFrom (GInfixOpen operators (Infix '[] ': grammars) base leftParen rightParen) =
        GInfixOpen operators grammars base leftParen rightParen

instance
    (
    ) => DerivedGrammar (GInfixOpen operators (Infix ( '(pre, inf, pos) ': infixGrammars ) ': grammars) base leftParen rightParen)
  where
    type DerivedFrom (GInfixOpen operators (Infix ( '(pre, inf, post) ': infixGrammars ) ': grammars) base leftParen rightParen) =
        GSum (GAllOf '[pre, GInfixOpen operators grammars base leftParen rightParen, inf, GInfixOpen operators grammars base leftParen rightParen, post])
             (GInfixOpen operators (Infix infixGrammars ': grammars) base leftParen rightParen)

-- Inferred form for infix operators.
instance
    ( DerivedGrammar (GInfixOpen operators grammars base leftParen rightParen)
    ) => InferredGrammar inferred (GInfixOpen operators (Infix '[] ': grammars) base leftParen rightParen)
  where
    type InferredForm inferred (GInfixOpen operators (Infix '[] ': grammars) base leftParen rightParen) =
        inferred
    inferFromUnderlying _ = id

instance
    ( InferredGrammar right (GInfixOpen operators (Infix infixGrammars ': grammars) base leftParen rightParen)
    ) => InferredGrammar (PSum ('Right right)) (GInfixOpen operators (Infix ( '(pre, inf, pos) ': infixGrammars ) ': grammars) base leftParen rightParen)
  where
    type InferredForm (PSum ('Right right)) (GInfixOpen operators (Infix ( '(pre, inf, pos) ': infixGrammars ) ': grammars) base leftParen rightParen) =
        right
    inferFromUnderlying _ term = case term of
        PSumRight right -> right

instance
    (
    ) => InferredGrammar (PSum ('Left (PAllOf '[inferredPre, recLeft, inferredInf, recRight, inferredPos]))) (GInfixOpen operators (Infix ( '(pre, inf, pos) ': infixGrammars ) ': grammars) base leftParen rightParen)
  where
    type InferredForm (PSum ('Left (PAllOf '[inferredPre, recLeft, inferredInf, recRight, inferredPos]))) (GInfixOpen operators (Infix ( '(pre, inf, pos) ': infixGrammars ) ': grammars) base leftParen rightParen) =
        PInfix (InfixOperator inferredPre recLeft inferredInf recRight inferredPos)
    inferFromUnderlying _ term = case term of
        PSumLeft (PAllOfCons pre
                 (PAllOfCons recLeft
                 (PAllOfCons inferredInf
                 (PAllOfCons recRight
                 (PAllOfCons inferredPos
                 (PAllOfNil)))))) -> PInfixOperator pre recLeft inferredInf recRight inferredPos

instance
    ( DerivedGrammar (GInfixOpen operators grammars base leftParen rightParen)
    ) => DerivedGrammar (GInfixOpen operators (Infixl infixlGrammars ': grammars) base leftParen rightParen)
  where
    type DerivedFrom (GInfixOpen operators (Infixl infixlGrammars ': grammars) base leftParen rightParen) =
        GProduct (GInfixOpen operators grammars base leftParen rightParen)
                 (GMany (GOneOf (InfixlGrammar infixlGrammars (GInfixOpen operators grammars base leftParen rightParen))))

instance
    ( DerivedGrammar (GInfixOpen operators grammars base leftParen rightParen)
    ) => InferredGrammar (PProduct count left (PMany '[]))
                         (GInfixOpen operators (Infixl infixlGrammars ': grammars) base leftParen rightParen)
  where
    type InferredForm (PProduct count left (PMany '[])) (GInfixOpen operators (Infixl infixlGrammars ': grammars) base leftParen rightParen) =
        left
    inferFromUnderlying _ term = case term of
        PProduct _ left _ -> left

instance
    ( DerivedGrammar (GInfixOpen operators grammars base leftParen rightParen)
    , InferredGrammar (PProduct count (PInfix (InfixOperator PTrivial left inf right post)) (PMany rest))
                      (GInfixOpen operators (Infixl infixlGrammars ': grammars) base leftParen rightParen)
    ) => InferredGrammar (PProduct count left (PMany ((POneOf n (PAllOf '[inf, right, post])) ': rest)))
                         (GInfixOpen operators (Infixl infixlGrammars ': grammars) base leftParen rightParen)
  where
    type InferredForm (PProduct count left (PMany ((POneOf n (PAllOf '[inf, right, post])) ': rest)))
                      (GInfixOpen operators (Infixl infixlGrammars ': grammars) base leftParen rightParen) =
        InferredForm (PProduct count (PInfix (InfixOperator PTrivial left inf right post)) (PMany rest))
                     (GInfixOpen operators (Infixl infixlGrammars ': grammars) base leftParen rightParen)
    inferFromUnderlying gproxy term = case term of
        PProduct count left (PManyCons (poneOf) rest) -> case pOneOfValue poneOf of
            PAllOfCons inf (PAllOfCons right (PAllOfCons post PAllOfNil)) ->
                let this = PInfixOperator PTrivial left inf right post
                in  inferFromUnderlying gproxy (PProduct count this rest)

instance
    ( DerivedGrammar (GInfixOpen operators grammars base leftParen rightParen)
    ) => DerivedGrammar (GInfixOpen operators (Infixr infixrGrammars ': grammars) base leftParen rightParen)
  where
    type DerivedFrom (GInfixOpen operators (Infixr infixrGrammars ': grammars) base leftParen rightParen) =
        GProduct (GMany (GOneOf (InfixrGrammar infixrGrammars (GInfixOpen operators grammars base leftParen rightParen))))
                 (GInfixOpen operators grammars base leftParen rightParen)

{-
instance
    ( DerivedGrammar (GInfixOpen grammars base leftParen rightParen)
    ) => InferredGrammar (PProduct (PMany '[]) right)
                         (GInfixOpen (Infixr infixrGrammars ': grammars) base leftParen rightParen)
  where
    type InferredForm (PProduct (PMany '[]) right)
                      (GInfixOpen (Infixr infixrGrammars ': grammars) base leftParen rightParen) =
        right
    inferFromUnderlying _ term = case term of
        PProduct _ right -> right

instance
    ( DerivedGrammar (GInfixOpen grammars base leftParen rightParen)
    , InferredGrammar (PProduct (PMany rest) right)
                      (GInfixOpen (Infixr infixrGrammars ': grammars) base leftParen rightParen)
    ) => InferredGrammar (PProduct (PMany ((POneOf n (PAllOf '[pre, left, inf])) ': rest)) right)
                         (GInfixOpen (Infixr infixrGrammars ': grammars) base leftParen rightParen)
  where
    type InferredForm (PProduct (PMany ((POneOf n (PAllOf '[pre, left, inf])) ': rest)) right)
                      (GInfixOpen (Infixr infixrGrammars ': grammars) base leftParen rightParen) =
        PInfix (InfixOperator pre
                              left
                              inf
                              (InferredForm (PProduct (PMany rest) right)
                                            (GInfixOpen (Infixr infixrGrammars ': grammars) base leftParen rightParen)
                              )
                              PTrivial
               )
    inferFromUnderlying gproxy term = case term of
        PProduct (PManyCons poneOf rest) right -> case pOneOfValue poneOf of
            PAllOfCons pre (PAllOfCons left (PAllOfCons inf PAllOfNil)) ->
                let that = inferFromUnderlying gproxy (PProduct rest right)
                in  PInfixOperator pre left inf that PTrivial
-}

-- An example of use: grade school algebra.

data Plus (ts :: [*]) t where
    Plus :: t -> Plus '[] t
instance GrammarSymbol (Plus '[]) where
    splitGrammarSymbol (Plus t) = t
data Minus (ts :: [*]) t where
    Minus :: t -> Minus '[] t
instance GrammarSymbol (Minus '[]) where
    splitGrammarSymbol (Minus t) = t
data Times (ts :: [*]) t where
    Times :: t -> Times '[] t
instance GrammarSymbol (Times '[]) where
    splitGrammarSymbol (Times t) = t
data Over (ts :: [*]) t where
    Over :: t -> Over '[] t
instance GrammarSymbol (Over '[]) where
    splitGrammarSymbol (Over t) = t
data Exponent (ts :: [*]) t where
    Exponent :: t -> Exponent '[] t
instance GrammarSymbol (Exponent '[]) where
    splitGrammarSymbol (Exponent t) = t
data Number (ts :: [*]) t where
    Number :: Int -> t -> Number '[] t
instance GrammarSymbol (Number '[]) where
    splitGrammarSymbol (Number _ t) = t
data OpenParen (ts :: [*]) t where
    OpenParen :: t -> OpenParen '[] t
instance GrammarSymbol (OpenParen '[]) where
    splitGrammarSymbol (OpenParen t) = t
data CloseParen (ts :: [*]) t where
    CloseParen :: t -> CloseParen '[] t
instance GrammarSymbol (CloseParen '[]) where
    splitGrammarSymbol (CloseParen t) = t

type Example1 = GInfix '[ Infixr '[ '(GTrivial, GSymbol Plus)
                                  , '(GTrivial, GSymbol Times)
                                  ]
                        ]
                       (GSymbol Number)
                       (GSymbol OpenParen)
                       (GSymbol CloseParen)

type Example2 = GInfix '[ Infixl '[ '(GSymbol Plus, GTrivial)
                                  , '(GSymbol Times, GTrivial)
                                  ]
                        ]
                       (GSymbol Number)
                       (GSymbol OpenParen)
                       (GSymbol CloseParen)

type Sentence1 = Number '[] (Plus '[] (Number '[] GEnd))
type Sentence2 = OpenParen '[] (Number '[] (Plus '[] (Number '[] (CloseParen '[] (Times '[] (Number '[] GEnd))))))
type Sentence3 = Number '[] (Times '[] (Number '[] (Times '[] (Number '[] GEnd))))

type GradeSchool = GInfix '[
      Infixl '[ '(GSymbol Plus, GTrivial), '(GSymbol Minus, GTrivial) ]
    , Infixl '[ '(GSymbol Times, GTrivial), '(GSymbol Over, GTrivial) ]
    , Infixl '[ '(GSymbol Exponent, GTrivial) ]
    ]
    (GSymbol Number)
    (GSymbol OpenParen)
    (GSymbol CloseParen)

-- Comments shows explicit expected associations

-- (1 + 2)
example00 = Number 1 . Plus . Number 2 $ GEnd
example01 = Number 1 . Plus . Number 2 . Plus . Number 3 $ GEnd

-- ((1 + 2) + 4) - 5
example1 = Number 1 . Plus . Number 2 . Plus . Number 4 . Minus . Number 5 $ GEnd
-- 1 * (2 + 3)
example2 = Number 1 . Times . OpenParen . Number 2 . Plus . Number 3 . CloseParen $ GEnd
-- 1 + (2 / 4)
example3 = Number 1 . Plus . Number 2 . Over . Number 4 $ GEnd
-- (1 + 2) / 4
example4 = OpenParen . Number 1 . Plus . Number 2 . CloseParen . Over . Number 4 $ GEnd

-- ((1 + 2) / 4) + (5 * 6 + 8 / 2) + 42
example5 =
    OpenParen . OpenParen . Number 1 . Plus . Number 2 . CloseParen . Over . Number 4 . CloseParen .
    Plus .
    OpenParen . Number 5 . Times . Number 6 . Plus . Number 8 . Over . Number 2 . CloseParen . Plus . Number 42
    $ GEnd

example6 =
    OpenParen . OpenParen . Number 1 . Plus . Number 2 . CloseParen . Over . Number 4 . CloseParen .
    Plus .
    OpenParen . Number 5 . Times . Number 6 . Plus . Number 8 . Over . Number 2 . CloseParen . Plus . Number 42 .
    OpenParen . OpenParen . Number 1 . Plus . Number 2 . CloseParen . Over . Number 4 . CloseParen .
    Plus .
    OpenParen . Number 5 . Times . Number 6 . Plus . Number 8 . Over . Number 2 . CloseParen . Plus . Number 42 .
    OpenParen . OpenParen . Number 1 . Plus . Number 2 . CloseParen . Over . Number 4 . CloseParen .
    Plus .
    OpenParen . Number 5 . Times . Number 6 . Plus . Number 8 . Over . Number 2 . CloseParen . Plus . Number 42 .
    OpenParen . OpenParen . Number 1 . Plus . Number 2 . CloseParen . Over . Number 4 . CloseParen .
    Plus .
    OpenParen . Number 5 . Times . Number 6 . Plus . Number 8 . Over . Number 2 . CloseParen . Plus . Number 42 .
    OpenParen . OpenParen . Number 1 . Plus . Number 2 . CloseParen . Over . Number 4 . CloseParen .
    Plus .
    OpenParen . Number 5 . Times . Number 6 . Plus . Number 8 . Over . Number 2 . CloseParen . Plus . Number 42 .
    OpenParen . OpenParen . Number 1 . Plus . Number 2 . CloseParen . Over . Number 4 . CloseParen .
    Plus .
    OpenParen . Number 5 . Times . Number 6 . Plus . Number 8 . Over . Number 2 . CloseParen . Plus . Number 42 .
    OpenParen . OpenParen . Number 1 . Plus . Number 2 . CloseParen . Over . Number 4 . CloseParen .
    Plus .
    OpenParen . Number 5 . Times . Number 6 . Plus . Number 8 . Over . Number 2 . CloseParen . Plus . Number 42 .
    OpenParen . OpenParen . Number 1 . Plus . Number 2 . CloseParen . Over . Number 4 . CloseParen .
    Plus .
    OpenParen . Number 5 . Times . Number 6 . Plus . Number 8 . Over . Number 2 . CloseParen . Plus . Number 42 .
    OpenParen . OpenParen . Number 1 . Plus . Number 2 . CloseParen . Over . Number 4 . CloseParen .
    Plus .
    OpenParen . Number 5 . Times . Number 6 . Plus . Number 8 . Over . Number 2 . CloseParen . Plus . Number 42 .
    OpenParen . OpenParen . Number 1 . Plus . Number 2 . CloseParen . Over . Number 4 . CloseParen .
    Plus .
    OpenParen . Number 5 . Times . Number 6 . Plus . Number 8 . Over . Number 2 . CloseParen . Plus . Number 42 .
    OpenParen . OpenParen . Number 1 . Plus . Number 2 . CloseParen . Over . Number 4 . CloseParen .
    Plus .
    OpenParen . Number 5 . Times . Number 6 . Plus . Number 8 . Over . Number 2 . CloseParen . Plus . Number 42 .
    OpenParen . OpenParen . Number 1 . Plus . Number 2 . CloseParen . Over . Number 4 . CloseParen .
    Plus .
    OpenParen . Number 5 . Times . Number 6 . Plus . Number 8 . Over . Number 2 . CloseParen . Plus . Number 42 .
    OpenParen . OpenParen . Number 1 . Plus . Number 2 . CloseParen . Over . Number 4 . CloseParen .
    Plus .
    OpenParen . Number 5 . Times . Number 6 . Plus . Number 8 . Over . Number 2 . CloseParen . Plus . Number 42 $ GEnd

--q = parseDerivedGrammar (Proxy :: Proxy GradeSchool) example1
--r = parseDerivedGrammar (Proxy :: Proxy GradeSchool) example2
--s = parseDerivedGrammar (Proxy :: Proxy GradeSchool) example3
--t = parseDerivedGrammar (Proxy :: Proxy GradeSchool) example4

--GrammarParse r GEnd = parseDerivedGrammar (Proxy :: Proxy GradeSchool) example0

-- Notes on  SLOWNESS
--
-- I expected it to be slow to compile, but it's slow even to use.
-- Observation: if we parseGrammar (not parseDerivedGrammar) then we're
-- slow to compile, quick to use. But if we parseDerivedGrammar, it's slow
-- on both: slow to compile, slow to use.
{-
GrammarParse q GEnd = parseDerivedGrammar (Proxy :: Proxy GradeSchool) example1

x :: Int
x = case q of
    PInfixOperator _ _ _ _ _ -> 42
-}
{-
GrammarParse q _ _ _ = parseGrammarV (example4)
                                     (Proxy :: Proxy (DeconstructGrammar GradeSchool))
-}
{-
GrammarParse q _ _ _ = parseGrammarV (example4)
                                     (Proxy :: Proxy (DeconstructGrammar GradeSchool))
-}
GrammarParse q _ _ _ = parseGrammarV (example00)
                                     (Proxy :: Proxy (DeconstructGrammar GradeSchool))

main :: IO ()
main = q `seq` print "Done"
{-
main = do
    print "Begin"
    case q of
        PClose (PProduct _ (PProduct _ (PProduct _ (PSumRight _) _) _) _) -> print "Middle"
    print "End"
    -}
