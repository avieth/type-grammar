# type-grammar

Parsing sequences of data constructors.

## Motivation

When we write terms of a DSL in Haskell, we use their structural form rather
than their written form. In a DSL for a subset of PostgreSQL DELETE commands,
for example, we would write something along the lines of

```Haskell
-- The form of PostgreSQL DELETES is this
--
--   DELETE FROM [ ONLY ] table
--      [ USING usinglist ]
--      [ WHERE condition ]
--
data DELETE table usinglist condition where
    DELETE
        :: table
        -> Bool -- True if ONLY is present
        -> Maybe usinglist
        -> Maybe condition
        -> DELETE

exampleTerm table condition = DELETE table False Nothing (Just condition)
```

With `type-grammar`, terms of `DELETE` can be safely parsed from
sequences of data constructors which can be made to resemble written SQL.

```Haskell
exampleSQL table condition = DELETE . FROM . table . WHERE . condition
GrammarParse exampleTerm' GEnd = parseDerivedGrammar deleteGrammar (exampleSQL GEnd0)
-- exampleTerm' == exampleTerm
```

It's almost like writing the SQL as a string, but without losing type-safety,
as the form of the term can be checked against a grammar at compile time.

This example is demonstrated with commentary in [SQL.hs](./Examples/SQL.hs).

## High-level overview of the method

Consider the typical pure functional parser, maybe a type like

```Haskell
type Parser s t = s -> Maybe (t, s)
```

Here we deal with the parsing of terms of type `s` to terms of type `t`.
Those `s` terms are composed of tokens, like `Char` in case `s ~ String`.

Imagine a similar construction with `*` instead of `s` and `t`, where tokens of
the input have kind `* -> *`. That's to say, parser input is a sequence of type
constructors, and parser output is some other type, rather than a term.
We get something like this

```Haskell
-- The parameter f indicates some type whose form is determined by the parsed
-- type t.
data Parse s t = Parse t s
data NoParse
-- This family will give either NoParse, or Parse s t.
type family ParseIt (grammar :: *) (sequenceOfConstructors :: *) :: *
```

If we take a finite set of types which can be chosen for `grammar` in the domain
of `ParseIt`, then we can implement it as a closed type family. A great choice
is this set

```Haskell
data GEmpty -- Never parses
data GTrivial -- Always parses, consuming no input
data GSymbol symbol next -- Parses if symbol is found
data GProduct left right -- Parses if left then right parses
data GSum left right -- Parses if either left or right parses
```

With `ParseIt` indicating the form of the parsed grammar, we can define
typeclasses to mirror the family (so-called companion classes), with method
to produce terms from sequences of term constructors corresponding to the
input type (regular function composition of constructors).
