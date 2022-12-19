<!-- idris
module README

import Data.CheckedEmpty.List
-->

# Collections with the type-level control of emptiness

## Types

### Lists

Those lists are called `CEList` and have a boolean argument as the first type argument.
Being `True`, this argument says that the list cannot be empty (such lists also are aliased as `NEList`).
Being `False`, this argument says that the list can be empty, but does not have to.

Having that, such lists have nice list syntax and universal pattern matching both in non-empty and regular case
(unlike standard `List1` type):

```idris
ne123 : NEList Nat
ne123 = [1, 2, 3]

head : NEList a -> a
head (x::xs) = x
```

```idris
me123 : CEList False Nat
me123 = [1, 2, 3]

head' : CEList False a -> Maybe a
head' []      = Nothing
head' (x::xs) = Just x
```

Actually, list literal it polymorphic, thus this also works

```idris
me123' : CEList ne Nat
me123' = [1, 2, 3]
```

When you use polymorphic value in a polymorphic context, non-emptiness value defaults to `True`
due to some [compiler trick](https://github.com/buzden/idris2-if-unsolved-implicit):

```idris
head'' : CEList ne a -> Maybe a
head'' []      = Nothing
head'' (x::xs) = Just x

x : Maybe Nat
x = head'' [1, 2, 3, 4]
```
