{-|
Module      : Examples.SQL
Description : Examples from SQL.
Copyright   : (c) Alexander Vieth, 2015
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module Examples.SQL where

import GHC.TypeLits (KnownSymbol, symbolVal, Symbol)
import Data.Proxy
import Data.String (IsString, fromString)
import Data.Type.Grammar

-- The form of PostgreSQL 8 point something DELETE is this
--
--   DELETE FROM [ ONLY ] table
--      [ USING usinglist ]
--      [ WHERE condition ]
--
-- For the sake of a brief demonstration, we'll just assume (very incorrectly)
-- that table, usinglist, and condition grammars consist of a single name.
--
-- To start, we'll state the grammar, known as the type Gdelete. We'll
-- factor out the table, usinglist, and condition parts. The symbols like
-- DELETE and FROM are defined later on.

type Gtable = GSymbol Name
type Gusinglist = GSymbol Name
type Gcondition = GSymbol Name

type Gdelete = GAllOf '[
      GSymbol DELETE, GSymbol FROM, GOptional (GSymbol ONLY), Gtable
      , GOptional (GAllOf '[GSymbol USING, Gusinglist])
      , GOptional (GAllOf '[GSymbol WHERE, Gcondition])
    ]

-- This looks quite a lot like the grammar definition from the docs, and we're
-- ready to use it right away, to recognize well-formed DELETE commands.

gdelete :: Proxy Gdelete
gdelete = Proxy

my_table = Name (Proxy :: Proxy "my_table")

example1 :: t -> DELETE '[] (FROM '[] (Name '[P "my_table"] t))
example1 = DELETE . FROM . my_table

-- The type is inferred by GHC, but it's state here just for demonstration.
-- It's a function type because what we're dealing with here is a kind of
-- stream of constructors for * -> * types, analagous to a stream of Char's
-- when we're parsing strings. When we're ready to parse a stream of
-- constructors, we plug it with GEnd, forming a complete sentence.

outcome1
    :: PAllOf
         '[ PSymbol DELETE '[] -- DELETE type takes 0 type parameters (empty list)
          , PSymbol FROM '[]   -- FROM also takes 0 type parameters
          , POptional 'Nothing -- ONLY part is not present
          , PSymbol Name '[P "my_table"] -- Name takes 1 type parameter, a Symbol
          , POptional 'Nothing -- USING part is not present
          , POptional 'Nothing -- WHERE part is not present
          ]
GrammarParse outcome1 GEnd = parseDerivedGrammar gdelete (example1 GEnd)

-- Some important points to highlight:
--
-- 1. This is not a partial pattern match. GHC knows that example1 GEnd
--    does indeed parse under the grammar Gdelete.
--
-- 2. The match on GEnd indicates that the entire sequence was consumed.
--    This is also worked out by GHC at compile time, as part of the
--    process of parsing.
--
-- 3. The type annotation is optional. GHC can infer the type of the parsed
--    thing. Here, the type is rather messy (but this can be improved, as we
--    shall see soon). However messy, it is still very enlightening. It shows
--    that we've discovered the table name "my_table", and each of the
--    optionals reveals that the corresponding optional part was not found in
--    the input sentence.
--
-- The next case shows what happens to the first optional when we throw in
-- an ONLY term.

example2 = DELETE . FROM . ONLY . my_table

outcome2
    :: PAllOf
          '[ PSymbol DELETE '[]
           , PSymbol FROM '[]
           , POptional ('Just (PSymbol ONLY '[])) -- Looks, it's now 'Just.
           , PSymbol Name '[P "my_table"]
           , POptional 'Nothing
           , POptional 'Nothing
           ]
GrammarParse outcome2 GEnd = parseDerivedGrammar gdelete (example2 GEnd)

-- And, of course, if we write garbage, GHC makes sure we don't hope to obtain
-- anything more than garbage.

example3 = DELETE . ONLY . FROM

GrammarNoParse = parseDerivedGrammar gdelete (example3 GEnd)

-- If we change it to @GrammarParse outcome3 GEnd@, we get a delightful
-- error:
--
--   Couldn't match type ‘GrammarNoParse’ with ‘GrammarParse t GEnd’
--      Expected type: GrammarParse t GEnd
--      Actual type: ParseDerivedGrammarK
--                       Gdelete (DELETE '[] (ONLY '[] (FROM '[] GEnd)))
--
-- That actual type, you can check in GHCi to be GrammarNoParse
--
--   :kind! ParseDerivedGrammarK Gdelete (DELETE '[] (ONLY '[] (FROM '[] GEnd))) 
--
--   ParseDerivedGrammarK Gdelete (DELETE '[] (ONLY '[] (FROM '[] GEnd))) :: *
--   = GrammarNoParse
--
-- After a parse, we obtain those P-prefixed datatypes, which are--unlike the
-- G-prefixed symbolic grammar types--actually inhabited. Thus we can
-- grab, say, outcome1, and do some computation

printOutcome1 :: String
printOutcome1 = case outcome1 of
    PAllOfCons
        (PSymbol (DELETE _))
        (PAllOfCons
        (PSymbol (FROM _))
        (PAllOfCons
        (POptionalNothing)
        (PAllOfCons
        (PSymbol (Name nameProxy _))
        (PAllOfCons
        (POptionalNothing)
        (PAllOfCons
        (POptionalNothing)
        PAllOfNil)))))
        -> "DELETE FROM " ++ symbolVal nameProxy

-- That's not so great, right? I count at least two issues:
--
-- 1. The datatype is unwieldly. We have to pattern match on the heterogeneous
--    list PAllOf, which is a bit left-field when we think we're working with
--    SQL deletes.
--
-- 2. Why bother constructing the datatype just to print it? Surely we can
--    print it directly from the sentence, and maintain type-safety by adding
--    a constraint to this print function asserting the sentence matches
--    Gdelete.
--
-- Number 2 is easily demonstrated:

printDeleteCommand
    :: ( FullParse Gdelete term 
       , PrintGrammarSymbols term String
       )
    => term
    -> String
printDeleteCommand term = printGrammarSymbols " " term

-- As for number 1, we have a solution, but to present it we must talk about
-- *derived symbolic grammars* and *inferred forms*.
--
-- A symbolic grammar is the input to a parser; the type which describes
-- precisely which sentences should be accepted. In case of a match, an
-- inferred form comes out the other end. Together with the remaining input,
-- the inferred form composes a @GrammarParse@ term. For every symbolic
-- grammar there is a unique associated inferred form.
--
-- The parser understands only 7 symbolic grammars, the so-called *primitive
-- symbolic grammars*. Here they are, with their associated inferred forms:
--
--   GEmpty, PEmpty; the empty grammar, which matches nothing.
--   GTrivial, PTrivial; the trivial grammar, which matches everything.
--   GSymbol symbol, PSymbol symbol parameters; matches a particular type,
--       symbol. Its inferred form picks up its parameters.
--   GProduct left right, PProduct left right; matches the two grammars in
--       sequences.
--   GSum left right, PSum outcome; matches either of the two grammars.
--       Its inferred form is tagged with a type of kind Either *, to identify
--       which alternative was found.
--   GRecurse, PRecurse recursive; symbolic recursion, signalling that the
--       parser should jump back to the topmost symbolic grammar.
--   GClose grammar, PClose inferred; closes a grammar to recursion, indicating
--       that the next GRecurse should jump back to here.
--
-- The symbolic grammar types are uninhabited, but all inferred forms except
-- for PEmpty *are* inhabited.
--
-- To define (derive) a new symbolic grammar, one must make a new type to
-- represent it, and give an instance of @DerivedGrammar@, which shows how to
-- decompose it into a simpler grammar (which may itself be a non-primitive
-- grammar). In an effort to be more practical and less abstract, we'll dive
-- right into an example, in which we parse delete commands to the
-- @DeleteCommand@ datatype. Its intentionally silly, omitting
-- completely the where and using clauses, because we haven't given a complete
-- grammar for those parts.

data DeleteCommand (tableName :: Symbol) where
    DeleteCommand
        :: Proxy tableName
        -> Bool -- Only
        -> Bool -- Found a USING clause
        -> Bool -- Found a WHERE clause
        -> DeleteCommand tableName
  deriving (Show)

data DeleteGrammar

deleteGrammar :: Proxy DeleteGrammar
deleteGrammar = Proxy

instance DerivedGrammar DeleteGrammar where
    type DerivedFrom DeleteGrammar = Gdelete

-- This is the inferred form of Gdelete. It's useful to have a type synonyms,
-- as the InferredGrammar instance demands writing it twice.
type Pdelete only tableName usingClause whereClause = PAllOf '[
      PSymbol DELETE '[]
    , PSymbol FROM '[]
    , POptional only
    , PSymbol Name '[tableName]
    , POptional usingClause
    , POptional whereClause
    ]

instance InferredGrammar (Pdelete only (P (tableName :: Symbol)) usingClause whereClause) DeleteGrammar where
    type InferredForm (Pdelete only (P tableName) usingClause whereClause) DeleteGrammar =
        DeleteCommand tableName
    inferFromUnderlying _ term = case term of
        PAllOfCons _
            (PAllOfCons _
            (PAllOfCons onlyPart
            (PAllOfCons (PSymbol (Name tableName _))
            (PAllOfCons usingPart
            (PAllOfCons wherePart
            (PAllOfNil)))))) -> DeleteCommand tableName hasOnly hasUsing hasWhere

          where

            hasOnly = case onlyPart of
                POptionalNothing -> False
                POptionalJust _ -> True

            hasUsing = case usingPart of
                POptionalNothing -> False
                POptionalJust _ -> True

            hasWhere = case wherePart of
                POptionalNothing -> False
                POptionalJust _ -> True

GrammarParse deleteCommand1 GEnd = parseDerivedGrammar deleteGrammar (example1 GEnd)
GrammarParse deleteCommand2 GEnd = parseDerivedGrammar deleteGrammar (example2 GEnd)

-- Here we define some symbols which are used in our grammars. They must have
-- GrammarSymbol instances, so we know how to shorten the stream of
-- constructors, analagous to a term parser demanding a Stream instance which
-- says how to produce the tail of the stream.
--
-- We also give PrintGrammarSymbol instances, which allow us to dump a DSL
-- term directly to a string-like monoid, without parsing it to a Grammar
-- first.
--
-- The kind signature is important, in case PolyKinds is on. If it's
-- [k] rather than [*] then the type families may get confused (I suspect
-- GHC won't agree that ('[] :: [k]) ~ ('[] :: [l])). In particular,
-- parameter matching and inference will not work as expected, leading to
-- stuck parsing.
data DELETE (ps :: [*]) t where
    DELETE :: t -> DELETE '[] t
instance GrammarSymbol (DELETE '[]) where
    splitGrammarSymbol (DELETE t) = t
instance IsString m => PrintGrammarSymbol (DELETE '[]) m where
    printGrammarSymbol _ _ = fromString "DELETE"

data FROM (ps :: [*]) t where
    FROM :: t -> FROM '[] t
instance GrammarSymbol (FROM '[]) where
    splitGrammarSymbol (FROM t) = t
instance IsString m => PrintGrammarSymbol (FROM '[]) m where
    printGrammarSymbol _ _ = fromString "FROM"

data ONLY (ps :: [*]) t where
    ONLY :: t -> ONLY '[] t
instance GrammarSymbol (ONLY '[]) where
    splitGrammarSymbol (ONLY t) = t
instance IsString m => PrintGrammarSymbol (ONLY '[]) m where
    printGrammarSymbol _ _ = fromString "ONLY"

data Name (ps :: [*]) t where
    Name :: Proxy sym -> t -> Name '[P (sym :: Symbol)] t
instance GrammarSymbol (Name '[P (sym :: Symbol)]) where
    splitGrammarSymbol (Name _ t) = t
instance (KnownSymbol sym, IsString m) => PrintGrammarSymbol (Name '[P sym]) m where
    printGrammarSymbol _ (Name proxySym _) = fromString (symbolVal proxySym)

data USING (ps :: [*]) t where
    USING :: t -> USING '[] t
instance GrammarSymbol (USING '[]) where
    splitGrammarSymbol (USING t) = t
instance IsString m => PrintGrammarSymbol (USING '[]) m where
    printGrammarSymbol _ _ = fromString "USING"

data WHERE (ps :: [*]) t where
    WHERE :: t -> WHERE '[] t
instance GrammarSymbol (WHERE '[]) where
    splitGrammarSymbol (WHERE t) = t
instance IsString m => PrintGrammarSymbol (WHERE '[]) m where
    printGrammarSymbol _ _ = fromString "WHERE"
