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

import Data.Proxy
import Data.Monoid
import Data.String (IsString, fromString)

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
type CompositeExpression = GAllOf '[
      GSymbol OpenParen
    , GRecurse
    , GSymbol CloseParen
    , GOneOf '[ GSymbol Plus, GSymbol Times ]
    , GSymbol OpenParen
    , GRecurse
    , GSymbol CloseParen
    ]
type SimpleExpression = GSymbol Number
type Expression = GOneOf '[
      SimpleExpression
    , CompositeExpression
    ]

data OpenParen t = OpenParen t
deriving instance Show t => Show (OpenParen t)
instance GrammarSymbol OpenParen where
    splitGrammarSymbol (OpenParen t) = t
instance IsString m => PrintGrammarSymbol OpenParen m where
    printGrammarSymbol _ _ = fromString "("

data CloseParen t = CloseParen t
deriving instance Show t => Show (CloseParen t)
instance GrammarSymbol CloseParen where
    splitGrammarSymbol (CloseParen t) = t
instance IsString m => PrintGrammarSymbol CloseParen m where
    printGrammarSymbol _ _ = fromString ")"

data Plus t = Plus t
deriving instance Show t => Show (Plus t)
instance GrammarSymbol Plus where
    splitGrammarSymbol (Plus t) = t
instance IsString m => PrintGrammarSymbol Plus m where
    printGrammarSymbol _ _ = fromString "+"

data Times t = Times t
deriving instance Show t => Show (Times t)
instance GrammarSymbol Times where
    splitGrammarSymbol (Times t) = t
instance IsString m => PrintGrammarSymbol Times m where
    printGrammarSymbol _ _ = fromString "x"

data Number t = Number Int t
deriving instance Show t => Show (Number t)
instance GrammarSymbol Number where
    splitGrammarSymbol (Number _ t) = t
instance IsString m => PrintGrammarSymbol Number m where
    printGrammarSymbol _ (Number i _) = fromString (show i)

class GrammarSymbol (ty :: * -> *) where
    splitGrammarSymbol :: ty rest -> rest

class GrammarSymbol symbol => PrintGrammarSymbol (symbol :: * -> *) m where
    printGrammarSymbol :: forall anything . Proxy m -> symbol anything -> m

-- The components of grammars.

-- | A Symbol, the atomic unit of a grammar.
data GSymbol (ty :: * -> *)

-- | A conjunction, or sequence, of two grammars.
data GProduct (left :: *) (right :: *)

-- | A disjunction, or choice, of two grammars.
data GSum (left :: *) (right :: *)

-- | The empty grammar, which matches nothing.
data GEmpty

-- | The trivial grammar, which matches everything.
data GTrivial

-- | A term to express recursion in a grammar.
data GRecurse

-- | A term to close a grammar to recursion.
data GClose t

-- | A derived grammar, to express the conjunction of 0 or more grammars.
type family GAllOf (grammars :: [*]) where
    GAllOf '[] = GTrivial
    GAllOf (grammar ': grammars) = GProduct grammar (GAllOf grammars)

-- | A derived grammar, to express the disjunction of 0 or more grammars.
type family GOneOf (grammars :: [*]) where
    GOneOf '[] = GEmpty
    GOneOf (grammar ': grammars) = GSum grammar (GOneOf grammars)

-- | A derived grammar, to express the conjunction of 0 or more of the
--   same grammar.
--   Notice our use of GClose and GRecurse. If we had simply recursed onto
--   GMany grammar where GRecurse is placed, this family would diverge, and
--   be useless to us. Instead, we use symbolic recursion, and are careful to
--   close the whole type, so that recursion loops back to the right place.
type family GMany (grammar :: *) where
    GMany grammar = GClose (GOneOf '[ GAllOf '[grammar, GRecurse], GTrivial ])

type family GOptional (grammar :: *) where
    GOptional grammar = GOneOf '[ grammar, GTrivial ]

-- | Indicate the end of a series of symbols. It's like a full stop in an
--   English sentence.
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
data GrammarParse recursion grammar remainder where
    GrammarParse
        :: Grammar recursion grammar
        -> remainder
        -> GrammarParse recursion grammar remainder

data GrammarNoParse = GrammarNoParse

-- | The universal grammar datatype. Its type parameters indicate its form.
--   Note that there is no constructor for GEmpty.
data Grammar (recursion :: *) (grammar :: *) :: * where
    GrammarSymbol
        :: symbol rest
        -> Grammar recursion (GSymbol symbol)
    GrammarProduct
        :: (Grammar recursion left, Grammar recursion right)
        -> Grammar recursion (GProduct left right)
    GrammarSum
        :: Either (Grammar recursion left) (Grammar recursion right)
        -> Grammar recursion (GSum left right)
    GrammarTrivial :: Grammar recursion GTrivial
    GrammarRecurse
        :: Grammar recursion recursion
        -> Grammar recursion GRecurse
    GrammarClose
        :: Grammar grammar grammar
        -> Grammar recursion (GClose grammar)

-- | This type family will parse a sequence of symbols to a grammar.
--   - @recursion@ is the reference for recursive grammars.
--   - @ty@ is the type to parse, analagous to a string under a string parser.
--   - @grammar@ is the grammar to parse against, analagous to the target type
--     of a string parser.
type family ParseGrammarK (recursion :: *) (ty :: *) (grammar :: *) :: * where

    -- GTrivial matches anything.
    ParseGrammarK recursion (GrammarMatch anything) (GTrivial) =
        GrammarParse recursion GTrivial anything

    -- GEmpty matches nothing.
    ParseGrammarK recursion (GrammarMatch anything) (GEmpty) =
        GrammarNoParse

    -- GSymbol matching. We use type-equality on the symbols, which
    -- have kind * -> *. The parameter to a matching symbol becomes the
    -- remaining (unparsed) type.
    ParseGrammarK recursion (GrammarMatch (ty rest)) (GSymbol ty) =
        GrammarParse recursion (GSymbol ty) rest
    ParseGrammarK recursion (GrammarMatch ty) (GSymbol ty') =
        GrammarNoParse

    -- GRecurse
    ParseGrammarK recursion anything GRecurse =
        ParseGrammarRecurseK recursion anything GRecurse 

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
    parseGrammar _ (GrammarMatch anything) _ = GrammarParse GrammarTrivial anything

instance
    (
    ) => ParseGrammar recursion (GrammarMatch anything) GEmpty
  where
    parseGrammar _ _ _ = GrammarNoParse

instance {-# OVERLAPS #-}
    ( GrammarSymbol ty
    ) => ParseGrammar recursion (GrammarMatch (ty rest)) (GSymbol ty)
  where
    parseGrammar _ (GrammarMatch symbol) _ = GrammarParse (GrammarSymbol symbol) (splitGrammarSymbol symbol)

instance {-# OVERLAPS #-}
    ( ParseGrammarK recursion (GrammarMatch ty) (GSymbol ty') ~ GrammarNoParse
    ) => ParseGrammar recursion (GrammarMatch ty) (GSymbol ty')
  where
    parseGrammar _ _ _ = GrammarNoParse

instance
    ( ParseGrammarRecurse recursion anything GRecurse
    ) => ParseGrammar recursion anything GRecurse
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

type family ParseGrammarRecurseK (recursion :: *) (ty :: *) (grammar :: *) :: * where

    ParseGrammarRecurseK recursion (GrammarParse recursion recursion rest) GRecurse =
        GrammarParse recursion GRecurse rest

    ParseGrammarRecurseK recursion GrammarNoParse GRecurse = GrammarNoParse

    ParseGrammarRecurseK recursion (GrammarMatch ty) GRecurse =
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
    ) => ParseGrammarRecurse recursion (GrammarParse recursion recursion rest) GRecurse
  where
    parseGrammarRecurse _ (GrammarParse this rest) _ = GrammarParse (GrammarRecurse this) rest

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
    ) => ParseGrammarRecurse recursion (GrammarMatch ty) GRecurse
  where
    parseGrammarRecurse recursion (GrammarMatch ty) grecurse =
        parseGrammarRecurse (recursion)
                            (parseGrammar recursion (GrammarMatch ty) recursion)
                            (grecurse)

type family ParseGrammarCloseK (recursion :: *) (ty :: *) (grammar :: *) :: * where

    ParseGrammarCloseK recursion (GrammarParse grammar grammar rest) (GClose grammar) =
        GrammarParse recursion (GClose grammar) rest

    ParseGrammarCloseK recursion GrammarNoParse (GClose grammar) =
        GrammarNoParse

    -- Called from ParseGrammarK: try to parse with the new recursion reference.
    -- The above two cases will collect the output and in case of a parse,
    -- replace the recursion reference.
    ParseGrammarCloseK recursion (GrammarMatch ty) (GClose grammar) =
        ParseGrammarCloseK (recursion)
                           (ParseGrammarK grammar (GrammarMatch ty) grammar)
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
    ) => ParseGrammarClose recursion (GrammarParse grammar grammar rest) (GClose grammar)
  where
    parseGrammarClose _ (GrammarParse this rest) _ = GrammarParse (GrammarClose this) rest

instance
    (
    ) => ParseGrammarClose recursion GrammarNoParse (GClose grammar)
  where
    parseGrammarClose _ grammarNoParse _ = grammarNoParse

instance
    ( ParseGrammarClose (recursion)
                        (ParseGrammarK grammar (GrammarMatch ty) grammar)
                        (GClose grammar)
    , ParseGrammar grammar (GrammarMatch ty) grammar
    ) => ParseGrammarClose recursion (GrammarMatch ty) (GClose grammar)
  where
    parseGrammarClose recursion (GrammarMatch ty) gclose =
        parseGrammarClose (recursion)
                          (parseGrammar grammar (GrammarMatch ty) grammar)
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
    ParseGrammarProductK recursion (GrammarParse recursion left rest) (ParseGrammarProductLeft left right) () =
        ParseGrammarProductK (recursion)
                             (ParseGrammarK recursion (GrammarMatch rest) right)
                             (ParseGrammarProductRight left right)
                             (GrammarParse recursion left rest)

    ParseGrammarProductK recursion (GrammarParse recursion right rest) (ParseGrammarProductRight left right) (GrammarParse recursion left rest') =
        GrammarParse recursion (GProduct left right) rest

    -- Here we know it's a recursive call from the final clause of this family.
    -- It means the left failed to parse, so the whole thing fails.
    ParseGrammarProductK recursion (GrammarNoParse) (ParseGrammarProductLeft left right) () =
        GrammarNoParse
    ParseGrammarProductK recursion (GrammarNoParse) (ParseGrammarProductRight left right) (GrammarParse recursion left rest') =
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
                          (GrammarParse recursion left rest)
    , ParseGrammar recursion (GrammarMatch rest) right
    ) => ParseGrammarProduct recursion (GrammarParse recursion left rest) (ParseGrammarProductLeft left right) ()
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
    ) => ParseGrammarProduct recursion (GrammarParse recursion right rest) (ParseGrammarProductRight left right) (GrammarParse recursion left rest')
  where
    parseGrammarProduct _ (GrammarParse right rest) _ (GrammarParse left rest') =
        GrammarParse (GrammarProduct (left, right)) rest

instance
    (
    ) => ParseGrammarProduct recursion GrammarNoParse (ParseGrammarProductLeft left right) ()
  where
    parseGrammarProduct _ grammarNoParse _ _ = grammarNoParse

instance
    (
    ) => ParseGrammarProduct recursion GrammarNoParse (ParseGrammarProductRight left right) (GrammarParse recursion left rest')
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
    ParseGrammarSumK recursion (GrammarParse recursion left rest) (ParseGrammarSumLeft left right) initial =
        GrammarParse recursion (GSum left right) rest

    -- The right parsed; we're done.
    ParseGrammarSumK recursion (GrammarParse recursion right rest) (ParseGrammarSumRight left right) initial =
        GrammarParse recursion (GSum left right) rest

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
    ) => ParseGrammarSum recursion (GrammarParse recursion left rest) (ParseGrammarSumLeft left right) initial
  where
    parseGrammarSum _ (GrammarParse this rest) _ _ =
        GrammarParse (GrammarSum sum) rest
      where
        sum :: Either (Grammar recursion left) (Grammar recursion right)
        sum = Left this

instance
    (
    ) => ParseGrammarSum recursion (GrammarParse recursion right rest) (ParseGrammarSumRight left right) initial
  where
    parseGrammarSum _ (GrammarParse this rest) _ _ =
        GrammarParse (GrammarSum sum) rest
      where
        sum :: Either (Grammar recursion left) (Grammar recursion right)
        sum = Right this

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
