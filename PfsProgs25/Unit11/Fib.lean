import Std
/-!
## Fibonacci numbers: memoization using the state monad

The naive way of computing Fibonacci numbers is very inefficient because it recomputes the same values many times. We can use the state monad to store the values of the Fibonacci numbers we have already computed. This is a simple example of memoization.

We will also take a more complicated example: Catalan numbers. The Catalan numbers are a sequence of natural numbers that occur in various counting problems, often involving recursively defined objects. They satisfy the recurrence relation:
* $C_0 = 1`,
* $C_{n+1} = \sum_{i=0}^n C_i C_{n-i}$, for $n \geq 0.$
-/
open Std
#check HashMap
#check StateM
