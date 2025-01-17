/-!
# Lab 01: Terms and Proofs

In this lab, you will define a few terms and prove some simple theorems. The proofs should all be **term** proofs, i.e., without using tactics.

To solve this lab, you should replace `sorry` with appropriate terms and proofs. The `sorry` command is a placeholder for code that has not been written yet. It is used as a temporary stub for an incomplete proof.

Some tests are also included as code that is commented out. If your code is correct these should pass after uncommenting.

## Some Terms

Define an `Int` term eight that is equal to 8.
-/
def eight : Int := (8 : Int)

/-!
**Test:** Uncomment the following lines to test your definition.
-/
/--
error: type mismatch
  eight
has type
  Int : Type
but is expected to have type
  Nat : Type
-/
#guard_msgs in
example : Nat := eight

/-#
## Simple functions

Define two functions `f` and `g` that map a natural number `n` to `2 * n + 1`, using the argument and the λ syntax respectively.
-/

def f (n: Nat) : Nat := 2 * n + 1

def g : Nat → Nat := fun n ↦ 2 * n + 1

-- Turns out both functions are definitionally equal

/-!
**Test:** Uncomment the following lines to test your definition.
-/
example : f 3 = 7 := rfl
example : g 3 = 7 := rfl

/-!
## Curried functions

Rewrite the functions `h` and `composeSelf` which are in argument form to curried form as `h'` and `composeSelf'`.
-/
def h (m : Int) (n: Nat) : Int := m - n

def h' : Int → Nat → Int :=
  fun m ↦ fun n ↦ m - n

def composeSelf (f : Nat → Nat) (n : Nat) : Nat := f (f n)

def composeSelf' : (Nat → Nat) → (Nat → Nat) := fun f ↦ fun n ↦ f (f n)

/-!
**Test:** Uncomment the following lines to test your definition.
-/
example : h' 5 3 = 2 := rfl
example : composeSelf' (fun n ↦ n + 1) 3 = 5 := rfl

/-!
## Term Proofs

In the following, prove the result using only the theorems `Nat.le_refl` and `Nat.le_step` and without using tactics. In particular, do not use `Nat.succ_le_succ`.
-/
#check Nat.le_refl -- ∀ (n : ℕ), n ≤ n

#check Nat.le_step -- ∀ (n m : ℕ), n ≤ m → n ≤ m + 1

example : 3 ≤ 3 :=
  Nat.le_refl 3

example : 3 ≤ 5 :=
  have h₀ := Nat.le_refl 3
  have h₁ := Nat.le_step h₀
  have h₂ := Nat.le_step h₁
  h₂

example (n: Nat) : n ≤ n + 2 :=
  have h₀ := Nat.le_refl n
  have h₁ := Nat.le_step h₀
  have h₂ := Nat.le_step h₁
  h₂
