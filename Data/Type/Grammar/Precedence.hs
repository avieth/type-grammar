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
data Infixl (grammars :: [*])
data Infixr (grammars :: [*])
data Infix (grammars :: [*])

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

data Literal (literal :: *)
data Operator (operator :: *) (left :: *) (right :: *)

-- | The inferred form of a GInfixOpen. It's the expression tree.
data PInfix (inferred :: *) where
    PInfixLiteral
        :: inferred
        -> PInfix (Literal inferred)
    PInfixOperator
        :: left
        -> op
        -> right
        -> PInfix (Operator op left right)

-- Derived grammar for 0 infix operators.
instance DerivedGrammar (GInfixOpen '[] base leftParen rightParen) where
    type DerivedFrom (GInfixOpen '[] base leftParen rightParen) =
        GSum base (GAllOf '[leftParen, GRecurse, rightParen])

-- Inferred grammar for 0 infix operators.
instance InferredGrammar (PSum ('Left inferredBase)) (GInfixOpen '[] base leftParen rightParen) where
    type InferredForm (PSum ('Left inferredBase)) (GInfixOpen '[] base leftParen rightParen) =
        PInfix (Literal inferredBase)
    inferFromUnderlying _ term = case term of
        PSumLeft inferredBase -> PInfixLiteral inferredBase

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
--   A = B[(1|2|..|n)B]
--
-- where B is the recursive case GInfixOpen grammarss base leftParen rightParen
-- (containing grammars for all tighter-binding operators) and 1,2..n are the
-- grammars in this Infix level.
-- Informally: B, or 2 B's infixed by any of the infix operators.
instance
    ( DerivedGrammar (GInfixOpen grammarss base leftParen rightParen)
    ) => DerivedGrammar (GInfixOpen (Infix grammars ': grammarss) base leftParen rightParen)
  where
    type DerivedFrom (GInfixOpen (Infix grammars ': grammarss) base leftParen rightParen) =
        GProduct (GInfixOpen grammarss base leftParen rightParen)
                 (GOptional (GProduct (GOneOf grammars) (GInfixOpen grammarss base leftParen rightParen)))

-- Inferred form for infix operators.
instance
    ( DerivedGrammar (GInfixOpen grammarss base leftParen rightParen)
    ) => InferredGrammar (PProduct (PInfix lower) (POptional 'Nothing)) (GInfixOpen (Infix grammars ': grammarss) base leftParen rightParen)
  where
    type InferredForm (PProduct (PInfix lower) (POptional 'Nothing)) (GInfixOpen (Infix grammars ': grammarss) base leftParen rightParen) =
        PInfix lower
    inferFromUnderlying _ term = case term of
        PProduct left _ -> left

instance
    ( DerivedGrammar (GInfixOpen grammarss base leftParen rightParen)
    ) => InferredGrammar (PProduct (PInfix left) (POptional ('Just (PProduct (POneOf idx op) right)))) (GInfixOpen (Infix grammars ': grammarss) base leftParen rightParen)
  where
    type InferredForm (PProduct (PInfix left) (POptional ('Just (PProduct (POneOf idx op) right)))) (GInfixOpen (Infix grammars ': grammarss) base leftParen rightParen) =
        PInfix (Operator (op) (PInfix left) right)
    inferFromUnderlying _ term = case term of
        PProduct left (POptionalJust (PProduct poneOf right)) ->
            PInfixOperator left (pOneOfValue poneOf) right

-- Derived grammar for left-infix operators.
-- We give something alongs the lines of this, if it means anything:
--
--   A = B{(1|2|..|n)B}
--
-- where B is the recursive case GInfixOpen grammarss base leftParen rightParen
-- (containing grammars for all tighter-binding operators) and 1,2..n are the
-- grammars in this Infix level.
-- Informally: B, followed by 0 or more B's prefixed by any of the infix
-- operators.
instance
    ( DerivedGrammar (GInfixOpen grammarss base leftParen rightParen)
    ) => DerivedGrammar (GInfixOpen (Infixl grammars ': grammarss) base leftParen rightParen)
  where
    type DerivedFrom (GInfixOpen (Infixl grammars ': grammarss) base leftParen rightParen) =
        GProduct (GInfixOpen grammarss base leftParen rightParen)
                 (GMany (GProduct (GOneOf grammars) (GInfixOpen grammarss base leftParen rightParen)))

instance
    ( DerivedGrammar (GInfixOpen grammarss base leftParen rightParen)
    ) => InferredGrammar (PProduct (PInfix lower) (PMany '[])) (GInfixOpen (Infixl grammars ': grammarss) base leftParen rightParen)
  where
    type InferredForm (PProduct (PInfix lower) (PMany '[])) (GInfixOpen (Infixl grammars ': grammarss) base leftParen rightParen) =
        PInfix lower
    inferFromUnderlying _ term = case term of
        PProduct left _ -> left

instance
    ( DerivedGrammar (GInfixOpen grammarss base leftParen rightParen)
    , InferredGrammar (PProduct (PInfix (Operator op (PInfix left) right)) (PMany rest)) (GInfixOpen (Infixl grammars ': grammarss) base leftParen rightParen)
    ) => InferredGrammar (PProduct (PInfix left) (PMany ((PProduct (POneOf idx op) (right)) ': rest))) (GInfixOpen (Infixl grammars ': grammarss) base leftParen rightParen)
  where
    type InferredForm (PProduct (PInfix left) (PMany ((PProduct (POneOf idx op) (right)) ': rest))) (GInfixOpen (Infixl grammars ': grammarss) base leftParen rightParen) =
        InferredForm (PProduct (PInfix (Operator op (PInfix left) right)) (PMany rest)) (GInfixOpen (Infixl grammars ': grammarss) base leftParen rightParen)
    inferFromUnderlying gproxy term = case term of
        PProduct left (PManyCons (PProduct poneOf right) rest) ->
            inferFromUnderlying gproxy (PProduct (PInfixOperator left (pOneOfValue poneOf) right) rest)

-- Derived grammar for right-infix operators.
-- It's the same as for left-infix operators; they differ, however, in their
-- InferredGrammar instances.
instance
    ( DerivedGrammar (GInfixOpen grammarss base leftParen rightParen)
    ) => DerivedGrammar (GInfixOpen (Infixr grammars ': grammarss) base leftParen rightParen)
  where
    type DerivedFrom (GInfixOpen (Infixr grammars ': grammarss) base leftParen rightParen) =
        GProduct (GInfixOpen grammarss base leftParen rightParen)
                 (GMany (GProduct (GOneOf grammars) (GInfixOpen grammarss base leftParen rightParen)))

instance
    ( DerivedGrammar (GInfixOpen grammarss base leftParen rightParen)
    ) => InferredGrammar (PProduct (PInfix lower) (PMany '[])) (GInfixOpen (Infixr grammars ': grammarss) base leftParen rightParen)
  where
    type InferredForm (PProduct (PInfix lower) (PMany '[])) (GInfixOpen (Infixr grammars ': grammarss) base leftParen rightParen) =
        PInfix lower
    inferFromUnderlying _ term = case term of
        PProduct left _ -> left

instance
    ( DerivedGrammar (GInfixOpen grammarss base leftParen rightParen)
    --, InferredGrammar (PProduct right (PMany rest)) (GInfixOpen (Infixr grammars ': grammarss) base leftParen rightParen)
    ) => InferredGrammar (PProduct (PInfix left) (PMany ((PProduct (POneOf idx op) (right)) ': rest))) (GInfixOpen (Infixr grammars ': grammarss) base leftParen rightParen)
  where
    type InferredForm (PProduct (PInfix left) (PMany ((PProduct (POneOf idx op) (right)) ': rest))) (GInfixOpen (Infixr grammars ': grammarss) base leftParen rightParen) =
        PInfix (Operator op
                         (PInfix left)
                         (InferredForm (PProduct right (PMany rest)) (GInfixOpen (Infixr grammars ': grammarss) base leftParen rightParen))
               )
    inferFromUnderlying gproxy term = case term of
        PProduct left (PManyCons (PProduct poneOf right) rest) ->
            PInfixOperator left
                           (pOneOfValue poneOf)
                           undefined --(inferFromUnderlying gproxy (PProduct right rest))

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

type GradeSchool = GInfix '[
      Infixl '[GSymbol Plus, GSymbol Minus]
    , Infixl '[GSymbol Times, GSymbol Over]
    , Infixl '[GSymbol Exponent]
    ]
    (GSymbol Number)
    (GSymbol OpenParen)
    (GSymbol CloseParen)

example1 = Number 1 . Plus . Number 2 . Plus . Number 4 . Minus . Number 5 $ GEnd
example2 = Number 1 . Times . OpenParen . Number 2 . Plus . Number 3 . CloseParen $ GEnd
example3 = Number 1 . Plus . Number 2 . Over . Number 4 $ GEnd
example4 = OpenParen . Number 1 . Plus . Number 2 . CloseParen . Over . Number 4 $ GEnd
