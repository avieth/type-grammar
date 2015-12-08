# type-grammar

## Motivation

When we write terms of a DSL in Haskell, we use their logical form rather than
their written form. In a DSL for a subset of PostgreSQL DELETE statements, for
example, we would write something alone the lines of

```Haskell
-- The form of PostgreSQL DELETES is this
--
--   DELETE FROM [ ONLY ] table
--      [ USING usinglist ]
--      [ WHERE condition ]
--
-- so we mirror its logical form.
data DELETE = DELETE table (Maybe ()) (Maybe usinglist) (Maybe condition)
exampleTerm table condition = DELETE table Nothing Nothing (Just condition)
```

This works just fine, but `type-grammar` offers an interesting alternative
approach, in which the written--rather than logical--form of the DSL terms is
used.

```Haskell
exampleTerm table condition = DELETE . FROM . table . WHERE . condition
```

It's almost like writing the SQL as a string, but without losing type-safety,
as the term can be checked against a grammar at compile time.

## High-level overview of the method

Consider the typical pure functional parser, maybe a type like

```Haskell
type Parser s t = s -> Maybe (t, s)
```

Here we deal with the parsing of *terms* of type `s` to terms of type `t`.
Those `s` terms are composed of tokens, like `Char` in case `s ~ String`.

Imagine a similar construction with `*` instead of `s`, where tokens have kind
`* -> *`. That's to say, parser input is a sequence of type constructors.
Now every term in the parser input is actually a Haskell type, and
the parsed term `t` is itself a type. We get something like this

```Haskell
-- The parameter f indicates some type whose form is determined by the parsed
-- type t.
data Parse f s t = Parse (f t) s
data NoParse
-- Types in the range of this family will be one of
--   Parse f s t
--   NoParse
type family Parser (f :: * -> *) (s :: *) (t :: *) :: *
```

If we take a finite set of types which can be chosen for `t`, then we can
set out to define such a type-level parser. A fine choice for `t` is this
set

```Haskell
data Empty
data Trivial
data Symbol (t :: * -> *)
data Product left right
data Sum left right
```

These describe algebraic datatypes. Thus, they allows us to parse a sequence of
types into some type which determines an algebraic datatype. Throwing these
parameters onto a GADT, we can recover the actual value

```Haskell
-- The parameter grammar forces a value of Grammar grammar to have the form of
-- a typical algebraic datatype.
-- Note that there's no constructor for Empty.
data Grammar (grammar :: *) where
    GrammarTrivial :: Grammar Trivial
    GrammarSymbol :: symbol rest -> Grammar (Symbol symbol)
    GrammarProduct :: (Grammar left, Grammar right) -> Grammar (Product left right)
    GrammarSum :: Either (Grammar left) (Grammar right) -> Grammar (Sum left right)
```

Setting `f ~ Grammar`, we get this

```Haskell
type GrammarParse s t = Parse Grammar s t
type family GrammarParser s t = Parser Grammar s t
```

An implementation of this type family allows GHC to check, at compile time,
whether a given sequence of constructors matches a given grammar type (one of
those 5 empty datatypes). A companion typeclass for this family allows GHC to
infer, at compile time, how to construct a `Grammar` of the corresponding form,
in case the sequence of constructors does parse in that form.

This module provides such a type family and companion class.
