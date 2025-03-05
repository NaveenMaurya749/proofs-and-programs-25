/-!
# Monads

Monads `m: Type u → Type v` are a common structure for sequencing computations that can:

* involve elements in a collection such as a list `List`,
* fail, such as `Option`,
* depend on and alter state, such as `StateM`,
* take a long time, such as `Task`,
* have side effects, such as `IO`,
...

## Operations

Monads have the following operations:

* `pure : α → m α` lifts a value into the monad; `return` is closely related.
* `bind : m α → (α → m β) → m β` sequences two computations, also called `flatMap` in concrete cases.
* `map : (α → β) → m α → m β` applies a function to the result of a computation.
* `flatten : m (m α) → m α` collapses nested monadic layers.

These are not independent. The definition of monads only requires `pure` and `bind`, but `map` and `flatten` can be defined in terms of them.

## Do notation

The value of monads is that we can use the `do` notation to avoid explicitly writing `bind` and `pure`. Formally, a `do` block is just syntax for a **term** in Lean, with type of the form `m α` for some `α`. The `do` block is translated into a series of `bind` and `pure` calls.
-/
