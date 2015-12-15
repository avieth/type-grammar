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
data Infixl (grammar :: *)
data Infixr (grammar :: *)
data Infix (grammar :: *)

-- To handle infix grammars we use a method in which each operator is given its
-- own unique precedence level, according to its position in a list, and the
-- grammar is transformed into n+1 grammars: one for each precedence level
-- and one for the terminal grammar. As an example, addition and multiplication
-- where multiplication binds tighter, and numbers are the terminals, looks
-- like this:
--
--     A = B {+ B}
--     B = C {* C}
--     C = Number | ( A )
--
-- where { x } means 0 or more occurrences of x.

data GInfixOpen (operators :: [*]) (base :: *) (leftParen :: *) (rightParen :: *)

data Literal (literal :: *)
data Operator (operator :: *) (left :: *) (right :: *)

-- What should this look like? The type parameter has to contain all of the
-- information about the structure of the parsed infix grammar:
data PInfixOpen (inferred :: *) where
    PInfixOpenLiteral
        :: inferred
        -> PInfixOpen (Literal inferred)
    PInfixOpenOperator
        :: left
        -> op
        -> right
        -> PInfixOpen (Operator op left right)

type family PInfixAssociateLeftK (left :: *) (op :: *) (pinfix :: *) :: * where
    PInfixAssociateLeftK left op (PInfixOpen (Literal inferred)) =
        PInfixOpen (Operator op left (PInfixOpen (Literal inferred)))
    PInfixAssociateLeftK left op (PInfixOpen (Operator op' left' right')) =
        PInfixOpen (Operator op' (PInfixAssociateLeftK left op left') right')

class PInfixAssociateLeft (left :: *) (op :: *) (pinfix :: *) where
    pInfixAssociateLeft
        :: left
        -> op
        -> pinfix
        -> PInfixAssociateLeftK left op pinfix

instance PInfixAssociateLeft left op (PInfixOpen (Literal inferred)) where
    pInfixAssociateLeft left op literal =
        PInfixOpenOperator left op literal

instance
    ( PInfixAssociateLeft left op left'
    ) => PInfixAssociateLeft left op (PInfixOpen (Operator op' left' right'))
  where
    pInfixAssociateLeft left op (PInfixOpenOperator left' op' right') =
        PInfixOpenOperator (pInfixAssociateLeft left op left') op' right'

instance DerivedGrammar (GInfixOpen '[] base leftParen rightParen) where
    type DerivedFrom (GInfixOpen '[] base leftParen rightParen) =
        GSum base (GAllOf '[leftParen, GRecurse, rightParen])

instance InferredGrammar (PSum ('Left inferredBase)) (GInfixOpen '[] base leftParen rightParen) where
    type InferredForm (PSum ('Left inferredBase)) (GInfixOpen '[] base leftParen rightParen) =
        PInfixOpen (Literal inferredBase)
    inferFromUnderlying _ term = case term of
        PSumLeft inferredBase -> PInfixOpenLiteral inferredBase

-- | TBD is this one correct? @inferredRecurse@ should be a PInfixOpen.
instance InferredGrammar (PSum ('Right (PAllOf '[inferredLeftParen, PRecurse inferredRecurse, inferredRightParen]))) (GInfixOpen '[] base leftParen rightParen) where
    type InferredForm (PSum ('Right (PAllOf '[inferredLeftParen, PRecurse inferredRecurse, inferredRightParen]))) (GInfixOpen '[] base leftParen rightParen) =
        inferredRecurse
    inferFromUnderlying proxy term = case term of
        PSumRight (PAllOfCons proxy (PAllOfCons (PRecurse recursive) _)) -> recursive

instance
    ( DerivedGrammar (GInfixOpen grammars base leftParen rightParen)
    ) => DerivedGrammar (GInfixOpen (Infix grammar ': grammars) base leftParen rightParen)
  where
    type DerivedFrom (GInfixOpen (Infix grammar ': grammars) base leftParen rightParen) =
        GProduct (DerivedFrom (GInfixOpen grammars base leftParen rightParen))
                 (GOptional (GProduct grammar (DerivedFrom (GInfixOpen grammars base leftParen rightParen))))

instance
    ( DerivedGrammar (GInfixOpen grammars base leftParen rightParen)
    ) => InferredGrammar (PProduct left (POptional 'Nothing)) (GInfixOpen (Infix grammar ': grammars) base leftParen rightParen)
  where
    type InferredForm (PProduct left (POptional 'Nothing)) (GInfixOpen (Infix grammar ': grammars) base leftParen rightParen) =
        left
    inferFromUnderlying _ term = case term of
        PProduct left _ -> left

instance
    ( DerivedGrammar (GInfixOpen grammars base leftParen rightParen)
    , InferredGrammar left (GInfixOpen grammars base leftParen rightParen)
    , InferredGrammar right (GInfixOpen grammars base leftParen rightParen)
    ) => InferredGrammar (PProduct left (POptional ('Just (PProduct op right)))) (GInfixOpen (Infix grammar ': grammars) base leftParen rightParen)
  where
    type InferredForm (PProduct left (POptional ('Just (PProduct op right)))) (GInfixOpen (Infix grammar ': grammars) base leftParen rightParen) =
        PInfixOpen (Operator op
                             (InferredForm left (GInfixOpen grammars base leftParen rightParen))
                             (InferredForm right (GInfixOpen grammars base leftParen rightParen))
                   )
    inferFromUnderlying _ term = case term of
        PProduct left (POptionalJust (PProduct op right)) ->
            PInfixOpenOperator left' op right'
          where
            left' = inferFromUnderlying proxyRecursive left
            right' = inferFromUnderlying proxyRecursive right
            proxyRecursive :: Proxy (GInfixOpen grammars base leftParen rightParen)
            proxyRecursive = Proxy

instance
    ( DerivedGrammar (GInfixOpen grammars base leftParen rightParen)
    ) => DerivedGrammar (GInfixOpen (Infixl grammar ': grammars) base leftParen rightParen)
  where
    type DerivedFrom (GInfixOpen (Infixl grammar ': grammars) base leftParen rightParen) =
        GProduct (DerivedFrom (GInfixOpen grammars base leftParen rightParen))
                 (GMany (GProduct grammar (DerivedFrom (GInfixOpen grammars base leftParen rightParen))))

instance
    ( DerivedGrammar (GInfixOpen grammars base leftParen rightParen)
    , InferredGrammar left (GInfixOpen grammars base leftParen rightParen)
    ) => InferredGrammar (PProduct left (PMany '[])) (GInfixOpen (Infixl grammar ': grammars) base leftParen rightParen)
  where
    -- Since we DeriveForm recursively, we also have to InferredForm
    -- recursively.
    type InferredForm (PProduct left (PMany '[])) (GInfixOpen (Infixl grammar ': grammars) base leftParen rightParen) =
        InferredForm left (GInfixOpen grammars base leftParen rightParen)
    inferFromUnderlying _ term = case term of
        PProduct left _ -> inferFromUnderlying gproxy left
      where
        gproxy :: Proxy (GInfixOpen grammars base leftParen rightParen)
        gproxy = Proxy

instance
    ( InferredGrammar left (GInfixOpen (grammars) base leftParen rightParen)
    , InferredGrammar (PProduct right (PMany rest)) (GInfixOpen (Infixl grammar ': grammars) base leftParen rightParen)
    , PInfixAssociateLeft (InferredForm left (GInfixOpen grammars base leftParen rightParen))
                          (op)
                          (InferredForm (PProduct right (PMany rest)) (GInfixOpen (Infixl grammar ': grammars) base leftParen rightParen))
    ) => InferredGrammar (PProduct left (PMany (PProduct op right ': rest))) (GInfixOpen (Infixl grammar ': grammars) base leftParen rightParen)
  where
    type InferredForm (PProduct left (PMany (PProduct op right ': rest))) (GInfixOpen (Infixl grammar ': grammars) base leftParen rightParen) =
        PInfixAssociateLeftK (InferredForm left (GInfixOpen grammars base leftParen rightParen))
                             (op)
                             (InferredForm (PProduct right (PMany rest)) (GInfixOpen (Infixl grammar ': grammars) base leftParen rightParen))
    inferFromUnderlying gproxy term = case term of
        PProduct left (PManyCons (PProduct op right) manyRest) ->
            pInfixAssociateLeft left' op right'
          where
            left' = inferFromUnderlying gproxy' left
            right' = inferFromUnderlying gproxy (PProduct right manyRest)
            gproxy' :: Proxy (GInfixOpen grammars base leftParen rightParen)
            gproxy' = Proxy


instance
    ( DerivedGrammar (GInfixOpen grammars base leftParen rightParen)
    ) => DerivedGrammar (GInfixOpen (Infixr grammar ': grammars) base leftParen rightParen)
  where
    type DerivedFrom (GInfixOpen (Infixr grammar ': grammars) base leftParen rightParen) =
        GProduct (GMany (GProduct (DerivedFrom (GInfixOpen grammars base leftParen rightParen)) grammar))
                 (DerivedFrom (GInfixOpen grammars base leftParen rightParen))

instance
    ( DerivedGrammar (GInfixOpen grammars base leftParen rightParen)
    , InferredGrammar right (GInfixOpen grammars base leftParen rightParen)
    ) => InferredGrammar (PProduct (PMany '[]) right) (GInfixOpen (Infixr grammar ': grammars) base leftParen rightParen)
  where
    -- Since we DeriveForm recursively, we also have to InferredForm
    -- recursively.
    type InferredForm (PProduct (PMany '[]) right) (GInfixOpen (Infixr grammar ': grammars) base leftParen rightParen) =
        InferredForm right (GInfixOpen grammars base leftParen rightParen)
    inferFromUnderlying _ term = case term of
        PProduct _ right -> inferFromUnderlying gproxy right
      where
        gproxy :: Proxy (GInfixOpen grammars base leftParen rightParen)
        gproxy = Proxy

instance
    ( InferredGrammar left (GInfixOpen (grammars) base leftParen rightParen)
    , InferredGrammar (PProduct (PMany rest) right) (GInfixOpen (Infixr grammar ': grammars) base leftParen rightParen)
    ) => InferredGrammar (PProduct (PMany (PProduct left op ': rest)) right) (GInfixOpen (Infixr grammar ': grammars) base leftParen rightParen)
  where
    -- Pay close attention to the choice of recursive InferredForms and
    -- how we control recursion on the first parameter of GInfixOpen.
    -- We treat left as though it was parsed from a lower grammar (with lesser
    -- precedence operators), because we know it was. BUT we don't recursive on
    -- that list for the remainder, because there may be more instances of
    -- this very class which we need to hit.
    type InferredForm (PProduct (PMany (PProduct left op ': rest)) right) (GInfixOpen (Infixr grammar ': grammars) base leftParen rightParen) =
        PInfixOpen (Operator op
                             (InferredForm left (GInfixOpen grammars base leftParen rightParen))
                             (InferredForm (PProduct (PMany rest) right) (GInfixOpen (Infixr grammar ': grammars) base leftParen rightParen))
                   )
    inferFromUnderlying gproxy term = case term of
        PProduct (PManyCons (PProduct left op) manyRest) right ->
            PInfixOpenOperator left' op right'
          where
            left' = inferFromUnderlying gproxy' left
            right' = inferFromUnderlying gproxy (PProduct manyRest right)
            gproxy' :: Proxy (GInfixOpen grammars base leftParen rightParen)
            gproxy' = Proxy



data Plus (ts :: [*]) t where
    Plus :: t -> Plus '[] t
instance GrammarSymbol (Plus '[]) where
    splitGrammarSymbol (Plus t) = t
data Times (ts :: [*]) t where
    Times :: t -> Times '[] t
instance GrammarSymbol (Times '[]) where
    splitGrammarSymbol (Times t) = t
data Number (ts :: [*]) t where
    Number :: Int -> t -> Number '[] t
instance GrammarSymbol (Number '[]) where
    splitGrammarSymbol (Number _ t) = t

type Example1 = GInfixOpen '[Infixr (GSymbol Plus)]
                           (GSymbol Number)
                           (GEmpty)
                           (GEmpty)

type Sentence1 = Number '[] (Plus '[] (Number '[] (Plus '[] (Number '[] (Plus '[] (Number '[] GEnd))))))
example1 = Number 1 . Plus . Number 2 . Plus . Number 4 . Plus . Number 5

type Example2 = GInfixOpen '[Infixl (GSymbol Plus)]
                           (GSymbol Number)
                           (GEmpty)
                           (GEmpty)
