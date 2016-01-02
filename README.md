# type-grammar

Parse types from types with compile-time monadic parsers.

```Haskell
-- Just like runParser (sepBy someParser someOtherParser) :: [t]
-- where someParser :: Parser t
:kind! RunParser (SepBy (MatchToken (Exact Maybe) 'Proxy)
                        (MatchToken (Exact []) 'Proxy)
                 )
                 (Maybe [Maybe [Maybe (Maybe End)]])
= 'Parsed ('NonEmptyList Maybe ('Cons Maybe ('Cons Maybe ('Nil 'Proxy)))) (Maybe End)
```

This program requires GHC's `TypeInType` extension, which is currently
in GHC HEAD and is set to be released with version 8.
