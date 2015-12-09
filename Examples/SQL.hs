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

module Examples.SQL where

import Data.Proxy
import Data.String (IsString, fromString)
import Data.Type.Grammar

-- The form of PostgreSQL DELETE is this
--
--   DELETE FROM [ ONLY ] table
--      [ USING usinglist ]
--      [ WHERE condition ]
--
-- For the sake of a brief demonstration, we'll just assume that table,
-- usinglist, and condition grammars consist of a single name.

type Gdelete = GAllOf '[
      GSymbol DELETE, GSymbol FROM, GOptional (GSymbol ONLY), Gtable
      , GOptional (GAllOf '[GSymbol USING, Gusinglist])
      , GOptional (GAllOf '[GSymbol WHERE, Gcondition])
    ]

type Gtable = GSymbol Name
type Gusinglist = GSymbol Name
type Gcondition = GSymbol Name

-- Here we define some symbols which we shall use. They must have
-- GrammarSymbol instances, so we know how to shorten the stream of
-- constructors, analagous to a term parser demanding a Stream instance which
-- says how to produce the tail of the stream.
--
-- We also give PrintGrammarSymbol instances, which allow us to dump a DSL
-- term directly to a string-like monoid, without parsing it to a Grammar
-- first.

data DELETE t = DELETE t
instance GrammarSymbol DELETE where
    splitGrammarSymbol (DELETE t) = t
instance IsString m => PrintGrammarSymbol DELETE m where
    printGrammarSymbol _ _ = fromString "DELETE"

data FROM t = FROM t
instance GrammarSymbol FROM where
    splitGrammarSymbol (FROM t) = t
instance IsString m => PrintGrammarSymbol FROM m where
    printGrammarSymbol _ _ = fromString "FROM"

data ONLY t = ONLY t
instance GrammarSymbol ONLY where
    splitGrammarSymbol (ONLY t) = t
instance IsString m => PrintGrammarSymbol ONLY m where
    printGrammarSymbol _ _ = fromString "ONLY"

data Name t = Name String t
instance GrammarSymbol Name where
    splitGrammarSymbol (Name _ t) = t
instance IsString m => PrintGrammarSymbol Name m where
    printGrammarSymbol _ (Name str _) = fromString str

data USING t = USING t
instance GrammarSymbol USING where
    splitGrammarSymbol (USING t) = t
instance IsString m => PrintGrammarSymbol USING m where
    printGrammarSymbol _ _ = fromString "USING"

data WHERE t = WHERE t
instance GrammarSymbol WHERE where
    splitGrammarSymbol (WHERE t) = t
instance IsString m => PrintGrammarSymbol WHERE m where
    printGrammarSymbol _ _ = fromString "WHERE"

-- GHC can infer this type. It's here just for illustration.
example1 :: t -> DELETE (FROM (Name t))
example1 = DELETE . FROM . Name "my_table"

-- This is not a partial match; GHC knows that example1 parses under Gdelete,
-- and is able to produce gexample1 always.
-- gexample1's Grammar type has two parameters because the first is used to
-- control recursion (that's also what the first proxy to parseGrammar means).
gexample1 :: Grammar Gdelete Gdelete
GrammarParse gexample1 _ = parseGrammar (Proxy :: Proxy Gdelete)
                                        (GrammarMatch (example1 GEnd))
                                        (Proxy :: Proxy Gdelete)

example2 = DELETE . FROM . ONLY . Name "my_table" . WHERE . Name "condition"

gexample2 :: Grammar Gdelete Gdelete
GrammarParse gexample2 _ = parseGrammar (Proxy :: Proxy Gdelete)
                                        (GrammarMatch (example2 GEnd))
                                        (Proxy :: Proxy Gdelete)

-- Here's an example which will not parse under Gdelete.
example3 = DELETE . ONLY . FROM . Name "my_table"

-- This is not a partial match; GHC knows that example3 does *not* parse
-- under Gdelete, i.e. that the type of this term is GrammarNoParse, a datatype
-- with exactly one constructor, GrammarNoParse.
GrammarNoParse = parseGrammar (Proxy :: Proxy Gdelete)
                              (GrammarMatch (example3 GEnd))
                              (Proxy :: Proxy Gdelete)

-- Since we gave PrintGrammarSymbol instances, we can directly produce SQL
-- strings from our examples--even the ones which don't parse.
-- In fact, this will print any sequence of grammar symbols which is printable,
-- not just SQL.
printDeleteUnsafe
    :: ( PrintGrammarSymbols term String )
    => term
    -> String
printDeleteUnsafe term = printGrammarSymbols (" " :: String) (term)

-- A safe printing function demands that the input parses under the grammar.
-- Trying it with example3, we find a delightful error message:
--
--   Couldn't match type ‘GrammarNoParse’
--                  with ‘GrammarParse Gdelete Gdelete GEnd’
--   Expected type: GrammarParse Gdelete Gdelete GEnd
--     Actual type: ParseGrammarK
--                    Gdelete (GrammarMatch (DELETE (ONLY (FROM (Name GEnd))))) Gdelete
--
printDeleteSafe
    :: ( PrintGrammarSymbols term String
       ,   ParseGrammarK Gdelete (GrammarMatch term) Gdelete
         ~ GrammarParse Gdelete Gdelete GEnd
       )
    => term
    -> String
printDeleteSafe = printDeleteUnsafe
