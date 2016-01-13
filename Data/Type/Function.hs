{-|
Module      : Data.Type.Function
Description : Type-level curried functions.
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
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Type.Function where

import Data.Kind
import Data.Proxy

data TyFunctionSort :: Type where
    TyFamily :: TyFunctionSort
    TyConstructor :: TyFunctionSort

type family CodomainKind (sort :: TyFunctionSort) (l :: Type) (f :: k) :: Type where
    CodomainKind sort (s -> t) f = TyFunction s (CodomainKind sort t f)
    CodomainKind 'TyFamily Type f = FunctionCodomain f
    CodomainKind 'TyConstructor l f = l

data TyFunction (domain :: Type) (codomain :: Type) :: Type where
    -- f' is f with 0 or more arguments applied.
    TyFunction
        :: TyFunctionSort
        -> Proxy domain
        -> Proxy codomain
        -> Proxy f
        -> Proxy f'
        -> TyFunction domain codomain

type family FunctionCodomain (f :: k) :: Type

type family EvalFunction (f :: Type) :: codomain

type family EvalFunctionKinded (f :: Type) codomain :: codomain where
    EvalFunctionKinded f codomain = EvalFunction f

type family RunTyFunction (f :: TyFunction domain codomain) (x :: domain) :: codomain where

    RunTyFunction ('TyFunction 'TyConstructor ('Proxy :: Proxy domain) ('Proxy :: Proxy codomain) ('Proxy :: Proxy f) ('Proxy :: Proxy (f' :: domain -> codomain))) (x :: domain) =
        f' x

    RunTyFunction ('TyFunction 'TyFamily ('Proxy :: Proxy domain) ('Proxy :: Proxy codomain) ('Proxy :: Proxy f) ('Proxy :: Proxy (f' :: domain -> Type))) (x :: domain) =
        EvalFunctionKinded (f' x) codomain

    RunTyFunction ('TyFunction sort ('Proxy :: Proxy domain) ('Proxy :: Proxy (TyFunction nextDomain nextCodomain)) ('Proxy :: Proxy f) ('Proxy :: Proxy (f' :: domain -> (t -> r)))) (x :: domain) =
        'TyFunction sort ('Proxy :: Proxy nextDomain) ('Proxy :: Proxy nextCodomain) ('Proxy :: Proxy f) ('Proxy :: Proxy (f' x))

--infixl 9 `At`
type At f x = RunTyFunction f x

infixr 0 :$
type f :$ x = At f x

-- | F for Family.
type family F (f :: k -> l) :: TyFunction k (CodomainKind 'TyFamily l f) where
    F (f :: k -> l) = 'TyFunction 'TyFamily ('Proxy :: Proxy k) ('Proxy :: Proxy (CodomainKind 'TyFamily l f)) ('Proxy :: Proxy f) ('Proxy :: Proxy f)

-- | C for Constructor.
type family C (f :: k -> l) :: TyFunction k (CodomainKind 'TyConstructor l f) where
    C (f :: k -> l) = 'TyFunction 'TyConstructor ('Proxy :: Proxy k) ('Proxy :: Proxy (CodomainKind 'TyConstructor l f)) ('Proxy :: Proxy f) ('Proxy :: Proxy f)

-- | Identity.
data Id (u :: Proxy k) (x :: k)
type instance FunctionCodomain (Id ('Proxy :: Proxy codomain)) = codomain
type instance EvalFunction (Id 'Proxy x) = x

-- | Constant.
data Const (pk :: Proxy k) (pl :: Proxy l) (x :: k) (y :: l)
type instance FunctionCodomain (Const ('Proxy :: Proxy k) 'Proxy) = k
type instance EvalFunction (Const ('Proxy :: Proxy k) ('Proxy :: Proxy l) (x :: k) (y :: l)) = x

-- | Composition, a higher-order type function.
data Dot (a :: Proxy s) (b :: Proxy t) (c :: Proxy u) (g :: TyFunction t u) (f :: TyFunction s t) (x :: s)
type instance FunctionCodomain (Dot 'Proxy 'Proxy ('Proxy :: Proxy codomain)) = codomain
type instance EvalFunction (Dot a b c g f x) = g `At` (f `At` x)

infixr 9 :.
type (g :: TyFunction t u) :. (f :: TyFunction s t) =
    (F (Dot ('Proxy :: Proxy s) ('Proxy :: Proxy t) ('Proxy :: Proxy u)) `At` g) `At` f

-- | Flip, a higher-order type function.
data Flip (ps :: Proxy s) (pt :: Proxy t) (pu :: Proxy u) (f :: TyFunction s (TyFunction t u)) (y :: t) (x :: s)
type instance FunctionCodomain (Flip 'Proxy 'Proxy ('Proxy :: Proxy u)) = u
type instance EvalFunction (Flip 'Proxy 'Proxy 'Proxy f y x) = f `At` x `At` y

data Fst (a :: Proxy s) (b :: Proxy t) (tuple :: (s, t))
type instance FunctionCodomain (Fst ('Proxy :: Proxy s) 'Proxy) = s
type instance EvalFunction (Fst 'Proxy 'Proxy '(s, t)) = s

data Snd (a :: Proxy s) (b :: Proxy t) (tuple :: (s, t))
type instance FunctionCodomain (Snd 'Proxy ('Proxy :: Proxy t)) = t
type instance EvalFunction (Snd 'Proxy 'Proxy '(s, t)) = t

data Not (b :: Bool)
type instance FunctionCodomain Not = Bool
type instance EvalFunction (Not 'True) = 'False
type instance EvalFunction (Not 'False) = 'True
