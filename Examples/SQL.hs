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

module Examples.SQL where

import GHC.TypeLits (KnownSymbol, symbolVal, Symbol)
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

type Gdelete tableName = GAllOf '[
      GSymbol DELETE '[], GSymbol FROM '[], GOptional (GSymbol ONLY '[]), Gtable tableName
      , GOptional (GAllOf '[GSymbol USING '[], Gusinglist Infer])
      , GOptional (GAllOf '[GSymbol WHERE '[], Gcondition Infer])
    ]

type Gtable name = GSymbol Name '[name]
type Gusinglist name = GSymbol Name '[name]
type Gcondition name = GSymbol Name '[name]

-- Here we define some symbols which we shall use. They must have
-- GrammarSymbol instances, so we know how to shorten the stream of
-- constructors, analagous to a term parser demanding a Stream instance which
-- says how to produce the tail of the stream.
--
-- We also give PrintGrammarSymbol instances, which allow us to dump a DSL
-- term directly to a string-like monoid, without parsing it to a Grammar
-- first.

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
instance GrammarSymbol (Name '[P sym]) where
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

-- GHC can infer this type. It's here just for illustration.
--example1 :: GEnd -> DELETE '[] (FROM '[] (Name '[P "my_table"] GEnd))
example1 = DELETE . FROM . Name (Proxy :: Proxy "my_table")

-- This is not a partial match; GHC knows that example1 parses under Gdelete,
-- and is able to produce gexample1 always.
-- gexample1's Grammar type has two parameters because the first is used to
-- control recursion (that's also what the first proxy to parseGrammar means).
gexample1 :: Grammar (Gdelete Infer) (Gdelete (P "my_table"))
GrammarParse gexample1 _ = parseGrammar (Proxy :: Proxy (Gdelete Infer))
                                        (GrammarMatch (example1 GEnd))
                                        (Proxy :: Proxy (Gdelete Infer))

example2 = DELETE . FROM . ONLY . Name (Proxy :: Proxy "my_table")
           . WHERE . Name (Proxy :: Proxy "condition")

-- NB this type signature is not correct. The two Infer types which are
-- baked into Gdelete will be inferred, meaning the type no longer matches
-- Gdelete. Actually, only one of the Infers will really be inferred, since
-- they are in a disjunction, and only the WHERE part matches, being
-- inferred to P "condition".
--
--gexample2 :: Grammar (Gdelete Infer) (Gdelete (P "my_table"))
GrammarParse gexample2 _ = parseGrammar (Proxy :: Proxy (Gdelete Infer))
                                        (GrammarMatch (example2 GEnd))
                                        (Proxy :: Proxy (Gdelete Infer))

-- Here's an example which will not parse under Gdelete.
example3 = DELETE . ONLY . FROM . Name (Proxy :: Proxy "my_table")

-- This is not a partial match; GHC knows that example3 does *not* parse
-- under Gdelete, i.e. that the type of this term is GrammarNoParse, a datatype
-- with exactly one constructor, GrammarNoParse.
GrammarNoParse = parseGrammar (Proxy :: Proxy (Gdelete Infer))
                              (GrammarMatch (example3 GEnd))
                              (Proxy :: Proxy (Gdelete Infer))

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
       , CompleteParse (GrammarMatch term) (Gdelete Infer)
       )
    => term
    -> String
printDeleteSafe = printDeleteUnsafe
