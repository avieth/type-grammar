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

module Data.Type.Grammar.Precedence where

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

-- | GInfix is given in terms of GInfixOpen, so named because it relies upon
--   a free occurrence of GRecurse in the grammar from which it is derived.
instance DerivedGrammar (GInfix operators base leftParen rightParen) where
    type DerivedFrom (GInfix operators base leftParen rightParen) =
        GClose (GInfixOpen operators base leftParen rightParen)

instance
    (
    ) => InferredGrammar (PClose (PInfix param)) (GInfix operators base leftParen rightParen)
  where
    type InferredForm (PClose (PInfix param)) (GInfix operators base leftParen rightParen) =
        PInfix param
    inferFromUnderlying _ (PClose term) = term

data GInfixOpen (operators :: [*]) (base :: *) (leftParen :: *) (rightParen :: *)

data InfixBase (base :: *)
data InfixOperator (pre :: *) (left :: *) (operator :: *) (right :: *) (post :: *)

-- | The inferred form of a GInfixOpen. It's the expression tree.
data PInfix (inferred :: *) where
    PInfixInfixBase
        :: inferred
        -> PInfix (InfixBase inferred)
    PInfixInfixOperator
        :: pre
        -> left
        -> op
        -> right
        -> post
        -> PInfix (InfixOperator pre left op right post)

-- Derived grammar for 0 infix operators.
instance DerivedGrammar (GInfixOpen '[] base leftParen rightParen) where
    type DerivedFrom (GInfixOpen '[] base leftParen rightParen) =
        GSum base (GAllOf '[leftParen, GRecurse, rightParen])

-- Inferred grammar for 0 infix operators.
instance InferredGrammar (PSum ('Left inferredBase)) (GInfixOpen '[] base leftParen rightParen) where
    type InferredForm (PSum ('Left inferredBase)) (GInfixOpen '[] base leftParen rightParen) =
        PInfix (InfixBase inferredBase)
    inferFromUnderlying _ term = case term of
        PSumLeft inferredBase -> PInfixInfixBase inferredBase

instance
    (
    ) => InferredGrammar (PSum ('Right (PAllOf '[inferredLeftParen, PRecurse inferredRecurse, inferredRightParen]))) (GInfixOpen '[] base leftParen rightParen)
  where
    type InferredForm (PSum ('Right (PAllOf '[inferredLeftParen, PRecurse inferredRecurse, inferredRightParen]))) (GInfixOpen '[] base leftParen rightParen) =
        inferredRecurse
    inferFromUnderlying proxy term = case term of
        PSumRight (PAllOfCons proxy (PAllOfCons (PRecurse recursive) _)) -> recursive

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
    ( DerivedGrammar (GInfixOpen grammars base leftParen rightParen)
    ) => DerivedGrammar (GInfixOpen (Infix '[] ': grammars) base leftParen rightParen)
  where
    type DerivedFrom (GInfixOpen (Infix '[] ': grammars) base leftParen rightParen) =
        GInfixOpen grammars base leftParen rightParen

instance
    (
    ) => DerivedGrammar (GInfixOpen (Infix ( '(pre, inf, pos) ': infixGrammars ) ': grammars) base leftParen rightParen)
  where
    type DerivedFrom (GInfixOpen (Infix ( '(pre, inf, post) ': infixGrammars ) ': grammars) base leftParen rightParen) =
        GSum (GAllOf '[pre, GInfixOpen grammars base leftParen rightParen, inf, GInfixOpen grammars base leftParen rightParen, post])
             (GInfixOpen (Infix infixGrammars ': grammars) base leftParen rightParen)

-- Inferred form for infix operators.
instance
    ( DerivedGrammar (GInfixOpen grammars base leftParen rightParen)
    ) => InferredGrammar inferred (GInfixOpen (Infix '[] ': grammars) base leftParen rightParen)
  where
    type InferredForm inferred (GInfixOpen (Infix '[] ': grammars) base leftParen rightParen) =
        inferred
    inferFromUnderlying _ = id

instance
    ( InferredGrammar right (GInfixOpen (Infix infixGrammars ': grammars) base leftParen rightParen)
    ) => InferredGrammar (PSum ('Right right)) (GInfixOpen (Infix ( '(pre, inf, pos) ': infixGrammars ) ': grammars) base leftParen rightParen)
  where
    type InferredForm (PSum ('Right right)) (GInfixOpen (Infix ( '(pre, inf, pos) ': infixGrammars ) ': grammars) base leftParen rightParen) =
        right

instance
    (
    ) => InferredGrammar (PSum ('Left (PAllOf '[inferredPre, recLeft, inferredInf, recRight, inferredPos]))) (GInfixOpen (Infix ( '(pre, inf, pos) ': infixGrammars ) ': grammars) base leftParen rightParen)
  where
    type InferredForm (PSum ('Left (PAllOf '[inferredPre, recLeft, inferredInf, recRight, inferredPos]))) (GInfixOpen (Infix ( '(pre, inf, pos) ': infixGrammars ) ': grammars) base leftParen rightParen) =
        PInfix (InfixOperator inferredPre recLeft inferredInf recRight inferredPos)

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

instance
    ( DerivedGrammar (GInfixOpen grammars base leftParen rightParen)
    ) => DerivedGrammar (GInfixOpen (Infixl infixlGrammars ': grammars) base leftParen rightParen)
  where
    type DerivedFrom (GInfixOpen (Infixl infixlGrammars ': grammars) base leftParen rightParen) =
        GProduct (GInfixOpen grammars base leftParen rightParen)
                 (GMany (GOneOf (InfixlGrammar infixlGrammars (GInfixOpen grammars base leftParen rightParen))))

instance
    ( DerivedGrammar (GInfixOpen grammars base leftParen rightParen)
    ) => InferredGrammar (PProduct left (PMany '[]))
                         (GInfixOpen (Infixl infixlGrammars ': grammars) base leftParen rightParen)
  where
    type InferredForm (PProduct left (PMany '[])) (GInfixOpen (Infixl infixlGrammars ': grammars) base leftParen rightParen) =
        left

instance
    ( DerivedGrammar (GInfixOpen grammars base leftParen rightParen)
    ) => InferredGrammar (PProduct left (PMany ((POneOf n (PAllOf '[inf, right, post])) ': rest)))
                         (GInfixOpen (Infixl infixlGrammars ': grammars) base leftParen rightParen)
  where
    type InferredForm (PProduct left (PMany ((POneOf n (PAllOf '[inf, right, post])) ': rest)))
                      (GInfixOpen (Infixl infixlGrammars ': grammars) base leftParen rightParen) =
        InferredForm (PProduct (PInfix (InfixOperator GTrivial left inf right post)) (PMany rest))
                     (GInfixOpen (Infixl infixlGrammars ': grammars) base leftParen rightParen)

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

instance
    ( DerivedGrammar (GInfixOpen grammars base leftParen rightParen)
    ) => DerivedGrammar (GInfixOpen (Infixr infixrGrammars ': grammars) base leftParen rightParen)
  where
    type DerivedFrom (GInfixOpen (Infixr infixrGrammars ': grammars) base leftParen rightParen) =
        GProduct (GMany (GOneOf (InfixrGrammar infixrGrammars (GInfixOpen grammars base leftParen rightParen))))
                 (GInfixOpen grammars base leftParen rightParen)

instance
    ( DerivedGrammar (GInfixOpen grammars base leftParen rightParen)
    ) => InferredGrammar (PProduct (PMany '[]) right)
                         (GInfixOpen (Infixr infixrGrammars ': grammars) base leftParen rightParen)
  where
    type InferredForm (PProduct (PMany '[]) right)
                      (GInfixOpen (Infixr infixrGrammars ': grammars) base leftParen rightParen) =
        right

instance
    ( DerivedGrammar (GInfixOpen grammars base leftParen rightParen)
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

