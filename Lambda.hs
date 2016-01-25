{-|
Module      : 
Description : 
Copyright   : (c) Alexander Vieth, 2016
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module Lambda where

import GHC.TypeLits
import Data.Kind
import Data.Proxy

type family Snoc (t :: k) (ts :: [k]) :: [k] where
    Snoc t '[] = '[t]
    Snoc t (s ': ss) = s ': Snoc t ss

type family Reverse (lst :: [k]) :: [k] where
    Reverse '[] = '[]
    Reverse (t ': ts) = Snoc t (Reverse ts)

data PatternBindings (complete :: Type) (rightmost :: Type) where
    PatternBindingsNil :: PatternBindings rightmost rightmost
    PatternBindingsCons :: Symbol -> Proxy t -> PatternBindings l r -> PatternBindings (t -> l) r

type PatternBindingsEx = 'PatternBindingsCons "x" ('Proxy :: Proxy Bool) (
                         'PatternBindingsCons "y" ('Proxy :: Proxy Nat) (
                         'PatternBindingsNil))

-- | This GADT is formed in such a way that a poly-kinded type constructor will
--   be specialized according to the kinds which compose a @PatternBindings@
--   type.
--
--   Note that there's nothing constraining the pattern bindings to be as
--   long as the constructor. Can we build that in?! Aha! When we specify
--   against as a non-arrow type, this will come out. So that's why we
--   include the Proxy for the rightmost type.
--
data PatternClause (against :: Type) where
    PatternClause
        :: Proxy rightmost
        -> constructor
        -> PatternBindings constructor rightmost
        -> PatternClause rightmost

-- | Check the type of the constructor held in a @PatternClause@.
type family PatternClauseConstructorType (p :: PatternClause t) :: Type where
    PatternClauseConstructorType ('PatternClause 'Proxy (constructor :: k) bindings) = k

-- Now, we must use a @PatternClause against@ to get a @Maybe PatternMatch@
-- on anything of kind @against@.

data PatternMatch (args :: [(Symbol, Type)]) (rightmost :: Type) where
    PatternMatchNil :: PatternMatch '[] rightmost
    PatternMatchCons :: Proxy (name :: Symbol) -> t -> PatternMatch ts (t -> r) -> PatternMatch ( '(name, t) ': ts ) r

type family PatternMatchConsMaybe (n :: Symbol) (t :: Type) (k :: t) (pm :: Maybe (PatternMatch ts (t -> r))) :: Maybe (PatternMatch ( '(n, t) ': ts) r ) where
    PatternMatchConsMaybe n t k 'Nothing = 'Nothing
    PatternMatchConsMaybe n t k ('Just rest) = 'Just ('PatternMatchCons 'Proxy k rest)

-- OK here's how we match: give the names and argument types in reverse
-- argument order, and then the rightmost kind and something of that kind.
-- If you get @'Just@, then the @PatternMatch@ type contains the actual
-- types found in the type called @rightmost@, and their associated names as
-- determined by the names list.
type family MatchAgainst (args :: [(Symbol, Type)]) (constructor :: k) (rightmost :: Type) (t :: rightmost) :: Maybe (PatternMatch args rightmost) where
    MatchAgainst ( '(n, k) ': ks ) constructor l ((q :: k -> l) (x :: k)) =
        PatternMatchConsMaybe n k x (MatchAgainst ks constructor (k -> l) q)
    MatchAgainst '[] q l (q :: l) = 'Just 'PatternMatchNil
    MatchAgainst a b c d = 'Nothing

-- So I think that's it. If we have a @PatternClause against@ then we
-- can come up with the named arguments and rightmost type... and I think
-- we're home.

-- | Convert a @PatternBindings@ into a list suitable for use as the first
--   parameter to @MatchAgainst@.
type family PatternBindingsForm (p :: PatternBindings constructor rightmost) :: [(Symbol, Type)] where
    PatternBindingsForm 'PatternBindingsNil = '[]
    PatternBindingsForm ('PatternBindingsCons sym ('Proxy :: Proxy t) rest) =
        Snoc '(sym, t) (PatternBindingsForm rest)

data BoundNames where
    BoundNamesNil :: BoundNames
    BoundNamesCons :: Proxy (name :: Symbol) -> Lambda t -> BoundNames -> BoundNames

-- | Try to resolve a name from a binding environment. If not found, give back
--   an 'LVar.
type family LookupName (name :: Symbol) (t :: LambdaType) (env :: BoundNames) :: Lambda t where
    LookupName name t ('BoundNamesCons ('Proxy :: Proxy name) (x :: Lambda t) rest) = x
    LookupName name t ('BoundNamesCons ('Proxy :: Proxy name') (x :: Lambda t') rest) =
        LookupName name t rest
    LookupName name t 'BoundNamesNil = 'LVar '(name, ('Proxy :: Proxy t))

type family AppendBoundNames (a :: BoundNames) (b :: BoundNames) :: BoundNames where
    AppendBoundNames 'BoundNamesNil b = b
    AppendBoundNames ('BoundNamesCons proxy t rest) b =
        'BoundNamesCons proxy t (AppendBoundNames rest b)

type family RemoveBoundName (name :: Symbol) (b :: BoundNames) :: BoundNames where
    RemoveBoundName name 'BoundNamesNil = 'BoundNamesNil
    RemoveBoundName name ('BoundNamesCons ('Proxy :: Proxy name) t rest) =
        RemoveBoundName name rest
    RemoveBoundName name ('BoundNamesCons ('Proxy :: Proxy name') t rest) =
        'BoundNamesCons ('Proxy :: Proxy name') t (RemoveBoundName name rest)

-- | BoundNames is just a PatternMatch without type information. This family
--   shows how.
type family PatternMatchToBoundNames (pm :: PatternMatch args rightmost) :: BoundNames where
    PatternMatchToBoundNames 'PatternMatchNil = 'BoundNamesNil
    PatternMatchToBoundNames ('PatternMatchCons proxyName t rest) =
        'BoundNamesCons proxyName ('LType t) (PatternMatchToBoundNames rest)

type family PatternMatchToBoundNamesMaybe (pm :: Maybe (PatternMatch args rightmost)) :: Maybe BoundNames where
    PatternMatchToBoundNamesMaybe 'Nothing = 'Nothing
    PatternMatchToBoundNamesMaybe ('Just pm) = 'Just (PatternMatchToBoundNames pm)

type family MatchClause (pc :: PatternClause against) (t :: against) :: Maybe BoundNames where
    MatchClause ('PatternClause (proxy :: Proxy k) constructor pbindings) t =
        PatternMatchToBoundNamesMaybe (MatchAgainst (PatternBindingsForm pbindings) constructor k t)

data LambdaType where
    LLit :: t -> LambdaType
    LArrow :: LambdaType -> LambdaType -> LambdaType

type Patterns (against :: Type) body = [(PatternClause against, Lambda body)]

type PatternsIsJust = '[
      '( 'PatternClause ('Proxy :: Proxy (Maybe k)) 'Just ('PatternBindingsCons "x" ('Proxy :: Proxy k) 'PatternBindingsNil), LType 'True)
    , '( 'PatternClause ('Proxy :: Proxy (Maybe k)) 'Nothing 'PatternBindingsNil, LType 'False)
    ]

data LambdaArgs constructor rightmost where
    LambdaArgsNil :: LambdaArgs t t
    LambdaArgsCons :: Lambda ('LLit t) -> LambdaArgs constructor (t -> k) -> LambdaArgs constructor k

-- Using LambdaArgsCons directly, the arguments will be backwards, so use
-- :@ and A instead: A :@ lambda1 :@ lambda2 ...
type A = 'LambdaArgsNil
type x :@ y = 'LambdaArgsCons y x

data Lambda (t :: LambdaType) where
    LType :: t -> Lambda ('LLit t)
    LCon :: constructor -> LambdaArgs constructor t -> Lambda ('LLit t)
    -- A proxied type family application.
    -- We need a proxy to indicate what's the codomain, as it may not
    -- necessarily be the kind of the saturated famly (which serves only as a
    -- type proxy to the family instance).
    LFam :: Proxy t -> constructor -> LambdaArgs constructor t -> Lambda ('LLit t')
    LVar :: (Symbol, Proxy t) -> Lambda t
    LAbs :: (Symbol, Proxy s) -> Lambda t -> Lambda ('LArrow s t)
    LApp :: Lambda ('LArrow s t) -> Lambda s -> Lambda t
    -- Recursive let.
    LLet :: (Symbol, Proxy t) -> Lambda t -> Lambda u -> Lambda u
    -- We run the first Lambda to get the thing against which to match.
    -- After matching, we have bindings in hand, which we add to the
    -- environment and then run the second Lambda.
    LCase :: Patterns against body -> Lambda ('LLit against) -> Lambda body

type family DropEnv (x :: (BoundNames, Lambda t)) :: Lambda t where
    DropEnv '(env, l) = l

type family RunLambdaEnv (env :: BoundNames) (l :: Lambda t) :: (BoundNames, Lambda t) where
    RunLambdaEnv env ('LType t) = '(env, 'LType t)
    RunLambdaEnv env ('LCon constructor args) = '(env, RunLambdaEnvCon env constructor args)
    -- RunLambdaEnv env ('LFam proxy constructor args)
    RunLambdaEnv env ('LVar '(name, ('Proxy :: Proxy t))) = '(env, LookupName name t env)
    -- We substitute under the lambda after erasing every occurrence of the
    -- lambda-bound name.
    RunLambdaEnv env ('LAbs '(name, proxy) body) =
        '(env, 'LAbs '(name, proxy) (DropEnv (RunLambdaEnv (RemoveBoundName name env) body)))
    -- This isn't right I think. Should we not feed the environment from left
    -- into the environment for right?
    RunLambdaEnv env ('LApp left right) = RunLambdaEnvApp env (RunLambdaEnv env left) (DropEnv (RunLambdaEnv env right))
    RunLambdaEnv env ('LCase pats x) = RunLambdaEnvCase env pats (DropEnv (RunLambdaEnv env x))
    RunLambdaEnv env ('LLet '(name, ('Proxy :: Proxy s)) rhs body) =
        RunLambdaEnv ('BoundNamesCons ('Proxy :: Proxy name) rhs env) body

type family RunLambdaEnvCon (env :: BoundNames) (constructor :: k) (args :: LambdaArgs k t) :: Lambda ('LLit t) where
    RunLambdaEnvCon env x 'LambdaArgsNil = 'LType x
    RunLambdaEnvCon env f ('LambdaArgsCons term rest) =
        'LType ((GetLambdaLit (RunLambdaEnvCon env f rest)) (GetLambdaLit (DropEnv (RunLambdaEnv env term))))

type family GetLambdaLit (lit :: Lambda ('LLit t)) :: t where
    GetLambdaLit ('LType t) = t

type family RunLambdaEnvApp (env :: BoundNames) (abs :: (BoundNames, Lambda ('LArrow s t))) (arg :: Lambda s) :: (BoundNames, Lambda t) where
    RunLambdaEnvApp env '(env', 'LAbs '(name, ('Proxy :: Proxy k)) body) arg =
        RunLambdaEnv ('BoundNamesCons ('Proxy :: Proxy name) arg (AppendBoundNames env' env)) body
    -- If the left doesn't reduce to a lambda, then there's nothing more we
    -- can do.
    RunLambdaEnvApp env '(env', left) right = '(AppendBoundNames env' env, 'LApp left right)

type family RunLambdaEnvCase (env :: BoundNames) (pats :: Patterns against body) (t :: Lambda ('LLit against)) :: (BoundNames, Lambda body) where
    RunLambdaEnvCase env ( '(clause, body) ': pats ) ('LType t) =
        RunLambdaEnvCaseSingle env (MatchClause clause t) body pats ('LType t)
    RunLambdaEnvCase env pats lambda = '(env, 'LCase pats lambda)

type family RunLambdaEnvCaseSingle (env :: BoundNames) (match :: Maybe BoundNames) (lbody :: Lambda body) (pats :: Patterns against body) (t :: Lambda ('LLit against)) :: (BoundNames, Lambda body) where
    RunLambdaEnvCaseSingle env 'Nothing body pats t = RunLambdaEnvCase env pats t
    RunLambdaEnvCaseSingle env ('Just env') body pats t =
        RunLambdaEnv (AppendBoundNames env' env) body

type RunLambda l = DropEnv (RunLambdaEnv 'BoundNamesNil l)

type LamId (pk :: Proxy k) = 'LAbs '("x", pk) ('LVar '("x", pk))
type LamConst (pk :: Proxy k) (pl :: Proxy l) =
    'LAbs '("x", pk) ('LAbs '("y", pl) ('LVar '("x", pk)))

-- g . f ~ \g . \f . \x . g(f(x))
type LamDot pg pf px =
    'LAbs '("g", pg) 
    ('LAbs '("f", pf)
    ('LAbs '("x", px)
    ('LApp ('LVar '("g", pg)) ('LApp ('LVar '("f", pf)) ('LVar '("x", px))))))

type At f x = 'LApp f x
type (:.) f g = LamDot 'Proxy 'Proxy 'Proxy `At` f `At` g

-- Some demonstrations of pattern matching.

-- Boolean not
type Not =
    'LAbs '("x", 'Proxy)
        ('LCase '[ '( 'PatternClause 'Proxy 'True 'PatternBindingsNil, 'LType 'False )
                 , '( 'PatternClause 'Proxy 'False 'PatternBindingsNil, 'LType 'True )
                 ]
                 ('LVar '("x", 'Proxy))
        )

-- Boolean and
type And =
    'LAbs '("x", 'Proxy)
        ('LAbs '("y", 'Proxy)
            ('LCase '[ '( 'PatternClause 'Proxy 'True 'PatternBindingsNil, 'LVar '("y", 'Proxy))
                     , '( 'PatternClause 'Proxy 'False 'PatternBindingsNil, 'LType 'False )
                     ]
                     ('LVar '("x", 'Proxy))
            )
        )

data List t where
    Nil :: List t
    Cons :: t -> List t -> List t

-- Safe list head
-- Here it seems the kind proxying is necessary.
type SafeHead (pt :: Proxy t) =
    'LAbs '("xs", ('Proxy :: Proxy ('LLit (List t))))
        ('LCase '[ '( 'PatternClause 'Proxy 'Nil 'PatternBindingsNil, 'LType 'Nothing )
                 , '( 'PatternClause 'Proxy 'Cons ('PatternBindingsCons "x" ('Proxy :: Proxy t) ('PatternBindingsCons "xs" ('Proxy :: Proxy (List t)) 'PatternBindingsNil))
                    , 'LCon 'Just (A :@ 'LVar '("x", ('Proxy :: Proxy ('LLit t))))
                    )
                 ]
                 ('LVar '("xs", ('Proxy :: Proxy ('LLit (List t)))))
        )

-- Next steps? Handle 'LFam? Then we should be able to define a parser as
type Parser t = Lambda ('LArrow ('LLit Symbol) ('LLit (Maybe (t, Symbol))))
-- Without 'LFam we have no way to make nontrivial parsers, because
-- Symbol is not defined like an ADT; we can't pattern match on it. We require
-- the magic type family SplitSymbol!
-- NB we shall also require recursion! Should look into that first.
-- Will it suffice to give a recursive let? A recursive function can then be
-- expressed as
--
--   let f = ...
--   in  f
--
-- Any ideas for a first recursive function? Ok, how about list length using
-- a recursive nat?

data RNat where
    RZ :: RNat
    RS :: RNat -> RNat

-- List length
type Length (pt :: Proxy t) =
    'LLet '("length", ('Proxy :: Proxy ('LArrow ('LLit (List t)) ('LLit RNat))))
           ('LAbs '("xs", ('Proxy :: Proxy ('LLit (List t))))
                   ('LCase '[ '( 'PatternClause 'Proxy 'Nil 'PatternBindingsNil, 'LType 'RZ )
                            , '( 'PatternClause 'Proxy 'Cons ('PatternBindingsCons "x" ('Proxy :: Proxy t) ('PatternBindingsCons "xs'" ('Proxy :: Proxy (List t)) 'PatternBindingsNil))
                               , 'LCon 'RS (A :@ 'LApp ('LVar '("length", ('Proxy :: Proxy ('LArrow ('LLit (List t)) ('LLit RNat))))) ('LVar '("xs'", ('Proxy :: Proxy ('LLit (List t))))))
                               )
                            ]
                            ('LVar '("xs", ('Proxy :: Proxy ('LLit (List t)))))
                   )
           )
           ('LVar '("length", ('Proxy :: Proxy ('LArrow ('LLit (List t)) ('LLit RNat)))))


