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

-- | A Symbol, the atomic unit of a grammar.
--   Elements of the list @l@ can be @Check t@, or @Infer@.
--   This will match @ty ps rest@ whenever @ps@ matches @l@. @ps@ must be a list
--   of @P s@. In order to match, the lists must be of the same length, and
--   every @Check t@ in @l@ must have a @P t@ at the same place in @ps@.
data GSymbol (ty :: [*] -> * -> *) (l :: [*])

-- | A conjunction, or sequence, of two grammars.
data GProduct (left :: *) (right :: *)

-- | A disjunction, or choice, of two grammars.
data GSum (left :: *) (right :: *)

-- | The empty grammar, which matches nothing.
data GEmpty

-- | The trivial grammar, which matches everything.
data GTrivial

-- | A term to express recursion in a grammar.
--   Parameter @t@ must be @Infer@ or @Check s@ where @s@ is the grammar
--   type you expect to match. Of course, you probably can't feed the grammar
--   you're defining recursively back into @Check s@, so in these cases
--   you'll use @Infer@.
--   But sometimes, as in the definition of the family @GMany@, @Check@
--   really is what we want.
data GRecurse t

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
    GMany grammar = GClose (GOneOf '[ GAllOf '[grammar, GRecurse (Check grammar)], GTrivial ])

-- | A derived grammar, to express the conjunction of 1 or more of the
--   same grammar.
type family GMany1 (grammar :: *) where
    GMany1 grammar = GAllOf '[grammar, GMany grammar]

-- | A derived grammar, to express that a grammar need not be present.
type family GOptional (grammar :: *) where
    GOptional grammar = GOneOf '[ grammar, GTrivial ]

-- | Indicate the end of a sequence of symbols.
--   The sequences which we shall be parsing are composed of * -> * types.
--   They are to be plugged with a GEnd to obtain a *.
data GEnd = GEnd
deriving instance Show GEnd

-- | Indicate a parameter to a symbol.
data P t

-- | Indicate that this parameter must match type @t@.
data Check t

-- | Indicate that this parameter is to be inferred.
data Infer

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

-- | Indicates no parse.
data GrammarNoParse = GrammarNoParse

-- | The universal grammar datatype. Its type parameters indicate its form.
--   Note that there is no constructor for GEmpty.
data Grammar (recursion :: *) (grammar :: *) :: * where
    GrammarSymbol
        :: symbol ps rest
        -> Grammar recursion (GSymbol symbol ps)
    GrammarProduct
        :: (Grammar recursion left, Grammar recursion right)
        -> Grammar recursion (GProduct left right)
    GrammarSum
        :: Either (Grammar recursion left) (Grammar recursion right)
        -> Grammar recursion (GSum left right)
    GrammarTrivial :: Grammar recursion GTrivial
    GrammarRecurse
        :: Grammar recursion recursion'
        -> Grammar recursion (GRecurse recursion')
    -- Here you don't get a hold of the grammar which was closed, only the
    -- otuput @grammar'@, which may differ in inferred parameters.
    -- That should be fine, though. I don't think we ever actually need the
    -- first parameter of Grammar.
    GrammarClose
        :: Grammar grammar grammar'
        -> Grammar recursion (GClose grammar')

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

    -- GSymbol.
    -- We match the parameters, and feed those into the symbol matching
    -- family. Only if the symbol types are the same, and their parameters
    -- match, do we give a parse.
    ParseGrammarK recursion (GrammarMatch ty) (GSymbol ty' args) =
        ParseGrammarSymbolK (recursion)
                            (GrammarMatch ty)
                            (GSymbol ty' args)
                            (SymbolParameterMatchK ty (GSymbol ty' args))

    -- GRecurse
    ParseGrammarK recursion anything (GRecurse arg) =
        ParseGrammarRecurseK recursion anything (GRecurse arg)

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

instance
    ( ParseGrammarSymbol (recursion)
                         (GrammarMatch ty)
                         (GSymbol ty' args)
                         (SymbolParameterMatchK ty (GSymbol ty' args))
    ) => ParseGrammar recursion (GrammarMatch ty) (GSymbol ty' args)
  where
    parseGrammar recursion ty grammar =
        parseGrammarSymbol recursion ty grammar parameterMatch
      where
        parameterMatch :: Proxy (SymbolParameterMatchK ty (GSymbol ty' args))
        parameterMatch = Proxy

instance
    ( ParseGrammarRecurse recursion anything (GRecurse arg)
    ) => ParseGrammar recursion anything (GRecurse arg)
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

-- Parameter matching of symbols (checking and inference).
data ParameterMatch (ps :: [*])
data ParameterNoMatch

type family SymbolParameterMatchCons (p :: *) (ps :: *) :: * where
    SymbolParameterMatchCons (P t) (ParameterMatch ps) = ParameterMatch (P t ': ps)
    SymbolParameterMatchCons (P t) (ParameterNoMatch) = ParameterNoMatch

type family SymbolParameterMatchK (symbol :: *) (grammar :: *) :: * where

    SymbolParameterMatchK (ty '[] rest) (GSymbol ty '[]) = ParameterMatch '[]
    SymbolParameterMatchK (ty (P t ': ps) rest) (GSymbol ty (Infer ': qs)) =
        SymbolParameterMatchCons (P t) (SymbolParameterMatchK (ty ps rest) (GSymbol ty qs))
    SymbolParameterMatchK (ty (P t ': ps) rest) (GSymbol ty (Check t ': qs)) =
        SymbolParameterMatchCons (P t) (SymbolParameterMatchK (ty ps rest) (GSymbol ty qs))
    SymbolParameterMatchK (ty (P t ': ps) rest) (GSymbol ty (Check s ': qs)) =
        ParameterNoMatch
    SymbolParameterMatchK (ty '[] rest) (GSymbol ty (p ': ps)) =
        ParameterNoMatch
    SymbolParameterMatchK (ty (p ': ps) rest) (GSymbol ty '[]) =
        ParameterNoMatch

type family ParseGrammarSymbolK (recursion :: *) (ty :: *) (grammar :: *) (parameters :: *) :: * where

    ParseGrammarSymbolK recursion (GrammarMatch (ty ps rest)) (GSymbol ty rs) (ParameterMatch ps) =
        GrammarParse recursion (GSymbol ty ps) rest

    ParseGrammarSymbolK recursion (GrammarMatch (ty qs rest)) (GSymbol ty rs) (ParameterNoMatch) =
        GrammarNoParse

    -- Catch-all failure case.
    ParseGrammarSymbolK recursion (GrammarMatch a) (GSymbol b c) parameters =
        GrammarNoParse

-- | Companion class to ParseGrammarSymbolK.
class ParseGrammarSymbol (recursion :: *) (ty :: *) (grammar :: *) (parameters :: *) where
    parseGrammarSymbol
        :: Proxy recursion
        -> ty
        -> Proxy grammar
        -> Proxy parameters
        -> ParseGrammarSymbolK recursion ty grammar parameters

instance
    ( GrammarSymbol (ty ps)
    ) => ParseGrammarSymbol recursion (GrammarMatch (ty ps rest)) (GSymbol ty rs) (ParameterMatch ps)
  where
    parseGrammarSymbol _ (GrammarMatch ty) _ _ = GrammarParse (GrammarSymbol ty) (splitGrammarSymbol ty)

instance
    (
    ) => ParseGrammarSymbol recursion (GrammarMatch (ty qs rest)) (GSymbol ty rs) (ParameterNoMatch)
  where
    parseGrammarSymbol _ _ _ _ = GrammarNoParse

instance {-# OVERLAPS #-}
    (   ParseGrammarSymbolK recursion (GrammarMatch a) (GSymbol b c) parameters
      ~ GrammarNoParse
    ) => ParseGrammarSymbol recursion (GrammarMatch a) (GSymbol b c) parameters
  where
    parseGrammarSymbol _ _ _ _ = GrammarNoParse

-- | Observe how we treat the parameter to GRecurse.
--   When we parse the input using the recursion reference, we may get a parse,
--   and the parse we get may not be exactly the same as the recursion type,
--   because parameters may be inferred. If the GRecurse parameter is Infer
--   then we take this as it is, otherwise (it's Check) we demand that it
--   matches the expected parameter.
type family ParseGrammarRecurseK (recursion :: *) (ty :: *) (grammar :: *) :: * where

    ParseGrammarRecurseK recursion (GrammarParse recursion recursion' rest) (GRecurse Infer) =
        GrammarParse recursion (GRecurse recursion') rest

    ParseGrammarRecurseK recursion (GrammarParse recursion recursion' rest) (GRecurse (Check recursion')) =
        GrammarParse recursion (GRecurse recursion') rest

    ParseGrammarRecurseK recursion (GrammarParse recursion recursion' rest) (GRecurse (Check recursion'')) =
        GrammarNoParse

    ParseGrammarRecurseK recursion GrammarNoParse (GRecurse arg) = GrammarNoParse

    ParseGrammarRecurseK recursion (GrammarMatch ty) (GRecurse arg) =
        ParseGrammarRecurseK (recursion)
                             (ParseGrammarK recursion (GrammarMatch ty) recursion)
                             (GRecurse arg)

-- | Companion class to ParseGrammarRecurseK.
class ParseGrammarRecurse (recursion :: *) (ty :: *) (grammar :: *) where
    parseGrammarRecurse
        :: Proxy recursion
        -> ty
        -> Proxy grammar
        -> ParseGrammarRecurseK recursion ty grammar

instance
    (
    ) => ParseGrammarRecurse recursion (GrammarParse recursion recursion' rest) (GRecurse Infer)
  where
    parseGrammarRecurse _ (GrammarParse this rest) _ = GrammarParse (GrammarRecurse this) rest

instance
    (
    ) => ParseGrammarRecurse recursion (GrammarParse recursion recursion' rest) (GRecurse (Check recursion'))
  where
    parseGrammarRecurse _ (GrammarParse this rest) _ = GrammarParse (GrammarRecurse this) rest

instance {-# OVERLAPS #-}
    (   ParseGrammarRecurseK (recursion)
                             (GrammarParse recursion recursion' rest)
                             (GRecurse (Check recursion''))
      ~ GrammarNoParse
    ) => ParseGrammarRecurse recursion (GrammarParse recursion recursion' rest) (GRecurse (Check recursion''))
  where
    parseGrammarRecurse _ _ _ = GrammarNoParse

instance
    (
    ) => ParseGrammarRecurse recursion GrammarNoParse (GRecurse arg)
  where
    parseGrammarRecurse _ grammarNoParse _ = grammarNoParse

instance
    ( ParseGrammarRecurse (recursion)
                          (ParseGrammarK recursion (GrammarMatch ty) recursion)
                          (GRecurse arg)
    , ParseGrammar recursion (GrammarMatch ty) recursion
    ) => ParseGrammarRecurse recursion (GrammarMatch ty) (GRecurse arg)
  where
    parseGrammarRecurse recursion (GrammarMatch ty) grecurse =
        parseGrammarRecurse (recursion)
                            (parseGrammar recursion (GrammarMatch ty) recursion)
                            (grecurse)

type family ParseGrammarCloseK (recursion :: *) (ty :: *) (grammar :: *) :: * where

    ParseGrammarCloseK recursion (GrammarParse grammar grammar' rest) (GClose grammar) =
        GrammarParse recursion (GClose grammar') rest

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
    ) => ParseGrammarClose recursion (GrammarParse grammar grammar' rest) (GClose grammar)
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
    --
    -- NB left' not necessarily left, as parsing can change the type by
    -- inferring parameters.
    ParseGrammarProductK recursion (GrammarParse recursion left rest) (ParseGrammarProductLeft left' right) () =
        ParseGrammarProductK (recursion)
                             (ParseGrammarK recursion (GrammarMatch rest) right)
                             (ParseGrammarProductRight left' right)
                             (GrammarParse recursion left rest)

    ParseGrammarProductK recursion (GrammarParse recursion right rest) (ParseGrammarProductRight left' right') (GrammarParse recursion left rest') =
        GrammarParse recursion (GProduct left right) rest

    -- Here we know it's a recursive call from the final clause of this family.
    -- It means the left failed to parse, so the whole thing fails.
    ParseGrammarProductK recursion (GrammarNoParse) (ParseGrammarProductLeft left right) () =
        GrammarNoParse
    ParseGrammarProductK recursion (GrammarNoParse) (ParseGrammarProductRight left right) (GrammarParse recursion left' rest') =
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
                          (ParseGrammarProductRight left' right)
                          (GrammarParse recursion left rest)
    , ParseGrammar recursion (GrammarMatch rest) right
    ) => ParseGrammarProduct recursion (GrammarParse recursion left rest) (ParseGrammarProductLeft left' right) ()
  where
    parseGrammarProduct recursion (GrammarParse this rest) _ () =
        parseGrammarProduct (recursion)
                            (parseGrammar recursion (GrammarMatch rest) (Proxy :: Proxy right))
                            (Proxy :: Proxy (ParseGrammarProductRight left' right))
                            (GrammarParse this rest)

-- This is the instance which demands that fourth parameter. Observe how we
-- use it to create the product grammar.
instance
    (
    ) => ParseGrammarProduct recursion (GrammarParse recursion right rest) (ParseGrammarProductRight left' right') (GrammarParse recursion left rest')
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
    ParseGrammarSumK recursion (GrammarParse recursion left rest) (ParseGrammarSumLeft left' right) initial =
        GrammarParse recursion (GSum left right) rest

    -- The right parsed; we're done.
    ParseGrammarSumK recursion (GrammarParse recursion right rest) (ParseGrammarSumRight left right') initial =
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
    ) => ParseGrammarSum recursion (GrammarParse recursion left rest) (ParseGrammarSumLeft left' right) initial
  where
    parseGrammarSum _ (GrammarParse this rest) _ _ =
        GrammarParse (GrammarSum sum) rest
      where
        sum :: Either (Grammar recursion left) (Grammar recursion right)
        sum = Left this

instance
    (
    ) => ParseGrammarSum recursion (GrammarParse recursion right rest) (ParseGrammarSumRight left right') initial
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

-- Some tools for identifying complete parses, without having to state the
-- first and second parameters of a GrammarParse.
type family GrammarParseRemainder (grammarParse :: *) :: * where
    GrammarParseRemainder (GrammarParse a b rest) = rest

class
    ( GrammarParseRemainder (ParseGrammarK grammar term grammar) ~ GEnd
    ) => CompleteParse term grammar
instance
    ( GrammarParseRemainder (ParseGrammarK grammar term grammar) ~ GEnd
    ) => CompleteParse term grammar
