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
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}

module Examples.SQL where

import Data.Kind
import Data.Proxy
import Data.Type.Function
import Data.Type.Parse
import GHC.TypeLits -- (KnownSymbol, symbolVal, Symbol, Character, IsAlphaNum)
import Data.String (IsString, fromString)

-- With data characters we'll just write SQL strings as types.
-- Our parsers will recognize well-formed SQL and produce Command types,
-- which can be consistency-checked against a database type.
-- To make the actual SQL, we can just symbolVal the string. That would be
-- a nice property: the SQL that runs is exactly the SQL that you write.
-- That means we'll have to parse the ? to mean some parameter, and we'll
-- have to infer the type of that parameter from the rest of the string.
-- Hm, but no, it'd be better if the programmar could write something like
--
--   ?name
--
-- so that they could substitute using names, rather than position.

data TableName where
    TableName :: Identifier -> TableName
type ParseTableName = C 'TableName :<$> (ParseIdentifier :<|> Quoted ParseIdentifier)
{-

data TableExpression where
    TableLiteral :: TableName -> TableExpression
    TableCrossJoin :: TableExpression -> TableExpression -> TableExpression
    TableInnerJoin :: TableExpression -> TableExpression -> JoinCondition -> TableExpression
    TableLeftJoin :: TableExpression -> TableExpression -> JoinCondition -> TableExpression
    TableRightJoin :: TableExpression -> TableExpression -> JoinCondition -> TableExpression
    TableFullJoin :: TableExpression -> TableExpression -> JoinCondition -> TableExpression

-- Parsing table expressions is an exercise in infix grammars.

type ParseTableExpression = ParseTableExpressionBase

-- Parsers for the infix join operators.
type ParseCrossJoin = ExactStringCI "CROSS" :*>  JOIN) 'Proxy :*> 'Trivial 'Proxy
type ParseInnerJoin = Optional (MatchToken (Exact INNER) 'Proxy) :*> MatchToken (Exact JOIN) 'Proxy :*> 'Trivial 'Proxy
type ParseLeftJoin = MatchToken (Exact LEFT) 'Proxy :*> Optional (MatchToken (Exact OUTER) 'Proxy) :*> 'Trivial 'Proxy
type ParseRightJoin = MatchToken (Exact RIGHT) 'Proxy :*> Optional (MatchToken (Exact OUTER) 'Proxy) :*> 'Trivial 'Proxy
type ParseFullJoin = MatchToken (Exact FULL) 'Proxy :*> Optional (MatchToken (Exact OUTER) 'Proxy) :*> 'Trivial 'Proxy



{-
type ParseTableExpressionLeftAssocJoin =
         MatchToken (Exact CROSS
    :<|>
-}

type ParseTableExpressionBase =

    (     (TyCon TableLiteral :<$> ParseTableName)
     :<|> (    MatchToken (Exact (:<)) 'Proxy
           :*> 'Suspend ParseTableExpressionThunk 'Proxy ('Proxy :: Proxy TableExpression)
           :<* MatchToken (Exact (:>)) 'Proxy
          )
    )

data ParseTableExpressionThunk
type instance Force ParseTableExpressionThunk inputKind TableExpression = ParseTableExpression
-}
data JoinCondition where
    NaturalJoin :: JoinCondition
    -- TODO Join predicate and using clause.

-- An identifier with an optional qualifier.
data Identifier where
    Identifier :: Maybe Symbol -> Symbol -> Identifier

-- Parses a safe string identifier. It's very conservative: only alphanumerics
-- and underscores.
type ParseIdentifier =
         C 'Identifier
    :<$> Optional (Quoted ParseStringNoQuotes :<* Many Whitespace :<* ExactChar '.' :<* Many Whitespace)
    :<*> Quoted ParseStringNoQuotes
type ParseStringNoQuotes =
         F NonEmptyListToString
    :<$> Many1 (MatchToken (F (BooleanCharacterization ('Proxy :: Proxy Character) (F IsIdentifierCharDef))) ('Proxy :: Proxy Symbol))
data IsIdentifierCharDef (c :: Character)
type instance FunctionCodomain IsIdentifierCharDef = Bool
type instance EvalFunction (IsIdentifierCharDef c) = IsIdentifierChar c
type family IsIdentifierChar (c :: Character) :: Bool where
    IsIdentifierChar '_' = 'True
    IsIdentifierChar c = IsAlphaNum c

type family IsNotQuote (c :: Character) :: Bool where
    IsNotQuote '\"' = 'False
    IsNotQuote c = 'True
data IsNotQuoteDef (c :: Character)
type instance FunctionCodomain IsNotQuoteDef = Bool
type instance EvalFunction (IsNotQuoteDef c) = IsNotQuote c

--type StringNoQuotes = Many (MatchToken (F (BooleanCharacterization ('Proxy :: Proxy Character) (F IsNotQuoteDef))) ('Proxy :: Proxy Symbol))
--type QuotedString = ExactChar '\"' :*> StringNoQuotes :<* ExactChar '\"'
type Quoted parser = ExactChar '\"' :*> parser :<* ExactChar '\"'

data Constant where
    NumberConstant :: SomeNumber -> Constant
    StringConstant :: Symbol -> Constant
    BoolConstant :: Bool -> Constant

type ParseConstant =
         (C 'BoolConstant :<$> ParseBoolConstant)
    :<|> (C 'NumberConstant :<$> ParseNumberConstant)
    :<|> (C 'StringConstant :<$> ParseStringConstant)

type ParseTrue =
         (ExactStringCI "true" :*> Pure 'Proxy 'True)
    :<|> (ExactCharCI 't' :*> Pure 'Proxy 'True)

type ParseFalse =
         (ExactStringCI "false" :*> Pure 'Proxy 'True)
    :<|> (ExactCharCI 'f' :*> Pure 'Proxy 'True)

type ParseBoolConstant = ParseTrue :<|> ParseFalse

data CharIsDigit (c :: Character)
type instance FunctionCodomain CharIsDigit = Maybe Nat
type instance EvalFunction (CharIsDigit c) = EvalCharIsDigit c
type family EvalCharIsDigit (c :: Character) :: Maybe Nat where
    EvalCharIsDigit '1' = 'Just 1
    EvalCharIsDigit '2' = 'Just 2
    EvalCharIsDigit '3' = 'Just 3
    EvalCharIsDigit '4' = 'Just 4
    EvalCharIsDigit '5' = 'Just 5
    EvalCharIsDigit '6' = 'Just 6
    EvalCharIsDigit '7' = 'Just 7
    EvalCharIsDigit '8' = 'Just 8
    EvalCharIsDigit '9' = 'Just 9
    EvalCharIsDigit '0' = 'Just 0
    EvalCharIsDigit c = 'Nothing

type Digit = MatchToken (F CharIsDigit) 'Proxy

data SumDecimal (l :: NonEmptyList Nat)
type instance FunctionCodomain SumDecimal = Nat
type instance EvalFunction (SumDecimal lst) = EvalSumDecimal lst
type family EvalSumDecimal (l :: NonEmptyList Nat) :: Nat where
    EvalSumDecimal ('NonEmptyList top list) =
        SumExponentiated (Exponentiate ('Cons top list) (EvalFunction (ListLength ('Cons top list))))
type family Exponentiate (l :: List Nat) (length :: Nat) :: List (Nat, Nat) where
    Exponentiate ('Nil 'Proxy) l = 'Nil 'Proxy
    Exponentiate ('Cons x rest) l = 'Cons '(x, l - 1) (Exponentiate rest (l - 1))
type family SumExponentiated (l :: List (Nat, Nat)) :: Nat where
    SumExponentiated ('Nil 'Proxy) = 0
    SumExponentiated ('Cons '(n, e) rest) = (n GHC.TypeLits.* (10 ^ e)) + SumExponentiated rest

type NaturalNumber = F SumDecimal :<$> (Many1 Digit)

data CharIsSign (c :: Character)
type instance FunctionCodomain CharIsSign = Bool
type instance EvalFunction (CharIsSign c) = EvalCharIsSign c
type family EvalCharIsSign (c :: Character) :: Bool where
    EvalCharIsSign '-' = 'True
    EvalCharIsSign '+' = 'True
    EvalCharIsSign c = 'False
type Sign = MatchToken (F (BooleanCharacterization 'Proxy (F CharIsSign))) 'Proxy

type DecimalPoint = ExactChar '.'

-- Since we have no type-level counterpart of a floating-point number, we just
-- give 'SomeNumber
data SomeNumber = SomeNumber
type ParseNumberConstant =
         Optional Sign
    :*>  NaturalNumber
    :*>  Optional (DecimalPoint :*> NaturalNumber)
    :*>  Pure 'Proxy 'SomeNumber

data IsSingleQuote (c :: Character)
type instance FunctionCodomain IsSingleQuote = Bool
type instance EvalFunction (IsSingleQuote c) = EvalIsSingleQuote c
type family EvalIsSingleQuote (c :: Character) :: Bool where
    EvalIsSingleQuote '\'' = 'True
    EvalIsSingleQuote c = 'False

type EscapedSingleQuote = ExactChar '\'' :*> ExactChar '\'' :*> Pure 'Proxy '\''

type ParseStringConstant =
         ExactChar '\''

    :*>  (    F ListToString
         :<$> (Many (    EscapedSingleQuote
                    :<|> (MatchToken (F (BooleanCharacterization 'Proxy (F Not :. F IsSingleQuote))) ('Proxy :: Proxy Symbol)))
                    
         ))
    :<*  ExactChar '\''

type ParseType =
         F ListToString
    :<$> Many (MatchToken (F (BooleanCharacterization 'Proxy (F IsIdentifierCharDef))) ('Proxy :: Proxy Symbol))

-- TODO since Cast is postfix, we actually require a Kleisli arrow
--   Expression -> Parser Symbol Cast
-- allowing us to :>>= onto an existing Expression parser.
data Cast where
    Cast :: Expression -> Symbol -> Cast
type ParseCast =
         (C 'Cast)
    :<$> ParseExpression
    :<*  Many Whitespace
    :<*  ExactString "::"
    :<*  Many Whitespace
    :<*> ParseType

data Arguments where
    Arguments :: List Expression -> Arguments

-- Parse a comma-separated, parens-enclosed argument list.
type ParseArguments =
         ExactChar '('
    :*>  Many Whitespace
    :*>  (C 'Arguments :<$> SepBy ParseExpression (Many Whitespace :*> ExactChar ',' :<* Many Whitespace))
    :<*  Many Whitespace
    :<*  ExactChar ')'

data FunctionAp where
    FunctionAp :: Symbol -> Arguments -> FunctionAp

-- Parse a function application. Functions are just Symbols.
type ParseFunctionAp =
         C 'FunctionAp
    :<$> (F ListToString :<$> Many (MatchToken (F (BooleanCharacterization 'Proxy (F IsIdentifierCharDef))) ('Proxy :: Proxy Symbol)))
    :<*  Many Whitespace
    :<*> ParseArguments

data Expression where
    ExpressionIdentifier :: Identifier -> Expression 
    ExpressionConstant :: Constant -> Expression
    ExpressionCast :: Cast -> Expression
    ExpressionFunctionAp :: FunctionAp -> Expression

-- We MUST have support for plugin-extended infix operators, as these do
-- arise in PostGIS. 
-- And then of course we'll have to deal with their precedence. 
-- So what's the plan? Parameter is a list of Type, each assumed to be a
-- plugin? These plugins determine 0 or more infix operators (strings). They
-- all left-associate with the same precedence, as according to the postgres
-- docs.
--
-- Compare at our treatment of functions. We need not have a list of valid
-- function strings, we can instead take any string from the proper character
-- set and assume its a function. Nonexistent functions can be eliminated at
-- type-checking time.
--
-- Another thing to consider: the cast infix operator ::. Its RHS must be a
-- type, so we'll have to be able to parse postgresql types, no? And these
-- can be extended. If we wish to use that thing in our Expr grammar, we'll
-- have to include postgresql types in the base parser, even though they're
-- only valid behind a cast.
-- No no no it's actually ok. Since it binds very tight, we can just include
-- it as part of the Literal parser. Indeed, the postgres precedence chart
-- is not that great a guide here. It even includes the '.' "operator" for
-- qualifying names.
--
-- In search of a plan, I think it's ideal to take a "types-first" approach, or
-- in this case "kinds-first". What are the kinds we would like to deal with?
--   - Literal
--     - Number
--     - String
--     - Bool
--     - Qualified name (with the dot)
--   - Casted something (expression for instance, but we can leave it free I believe)
--   - True infix operators: arithmetic, comparison, logical, extensible.
--     To be consistent with the docs, we must parse on the strings themselves
--     (so that, for instance, even an overloaded + has higher precedence than
--     some other custom opeartor).
--   - Function application: a string then a list of arguments.
--   - Various postfix things like IS NULL. 
-- Then we should be able to roll these all into one...
-- infix rec :>>= tryPostfix.
-- Right. So the base case is a literal, a function application, or
-- parenthesised recursion.
-- Then we throw on infix operators.
-- Then atop then we check, via bind, whether a postfix operator lurks.
-- And that's it.
-- All we must hope for now is that it doesn't take 8gb of memory and a day to
-- compile.
--
-- As for extensibility, perhaps we should just make a PostgresEnv type which
-- determines Symbols for all of the available functions, operators, types, etc.
-- BUT of course this is not needed for parsing. Parsing just checks
-- well-formedness and we want to keep it as light as possible, for I believe
-- that type-checking the parsed types will not be as performance-dangerous.

type ParseExpression = 'Suspend ParseExpressionThunk ('Proxy :: Proxy Symbol) ('Proxy :: Proxy Expression)
data ParseExpressionThunk
type instance Force ParseExpressionThunk Symbol Expression =

         (C 'ExpressionFunctionAp :<$> ParseFunctionAp)
    :<|> (C 'ExpressionConstant :<$> ParseConstant)
    :<|> (C 'ExpressionIdentifier :<$> ParseIdentifier)

-- Observation: adding a new level to the infix parser severely degrades
-- performance.
--
-- NB: precedence here is ascending, whereas in the postgres docs table it's
-- descending.
type ParseInfix = MkParseExpr '[
                                 Infixl '[ Many Whitespace :*> ExactStringCI "OR" :<* Many Whitespace ]
                               , Infixl '[ Many Whitespace :*> ExactStringCI "AND" :<* Many Whitespace ]
                               , Infix '[ Many Whitespace :*> ExactString "=" :<* Many Whitespace ]
                               ]
                              (ParseExpression)
                              (Many Whitespace :*> ExactChar '(' :*> Many Whitespace :*> Pure 'Proxy '())
                              (Many Whitespace :*> ExactChar ')' :*> Many Whitespace :*> Pure 'Proxy '())


data Restriction where
    Restriction :: Expr Expression Symbol -> Restriction

type ParseRestriction = C 'Restriction :<$> ParseInfix

data Command where
    Delete :: TableName -> Maybe Restriction -> Command

type ParseDelete = 
         (C 'Delete)
    :<$  ExactStringCI "DELETE"
    :<*  Many1 Whitespace
    :<*  ExactStringCI "FROM"
    :<*  Many1 Whitespace
    :<*> ParseTableName
    :<*> Optional (    Many1 Whitespace
                  :*>  ExactStringCI "WHERE"
                  :*>  Many1 Whitespace
                  :*>  ParseRestriction
                  )

type ExampleDelete1 = "DELETE FROM \"mytable\" WHERE \"mytable\".\"id\" = 1"
type ExampleDelete2 = "DELETE FROM \"mytable\" WHERE \"mytable\".\"id\" = 1 AND \"id\" = 'some_string'"

{-
class MakeQuery (cmd :: Command) m where
    makeQuery :: Proxy cmd -> m

instance
    ( IsString m
    , Monoid m
    , KnownSymbol sym
    ) => MakeQuery ('Delete ('TableName sym)) m
  where
    makeQuery _ = mconcat [
          fromString "DELETE FROM "
        , fromString (quoteSymbol (Proxy :: Proxy sym))
        ]

quoteSymbol :: KnownSymbol sym => Proxy sym -> String
quoteSymbol sym = concat ["\"", symbolVal sym, "\""]

q :: String
q = makeQuery (Proxy :: Proxy (TyResultValue `At` RunParser ParseDelete ExampleDelete))
-}
