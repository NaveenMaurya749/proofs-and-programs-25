/--
# Lecture 7: Logic in Lean
### We consider the Curry-Howard correspondence in context of propositional logic.

### Quantifiers
--/

inductive MyNat : Type where
  | zero : MyNat
  | succ : MyNat → MyNat

namespace MyNat

def add (m n : MyNat) : MyNat :=
  match n with
  | zero => m
  | succ n' => succ (add m n')

def mul (m n : MyNat) : MyNat :=
  match n with
  | zero => zero
  | succ n' => add m (mul m n')

inductive le (m n : MyNat) : Prop where
  | refl (m : MyNat) : le m m
  | step (m n : MyNat) : le m n → le m (succ n)

def one := succ zero
def two := succ one

instance : LE MyNat where
  le := le

example : zero ≤ two := by
  apply le.step
  apply le.step
  apply le.refl

theorem zero_le (n : MyNat) : zero ≤ n := by
  induction n with
  | zero => apply le.refl
  | succ n' ih =>
    apply le.step
    exact ih

theorem le_trans {m n k : MyNat} : m ≤ n → n ≤ k → m ≤ k := by
  intro h₁ h₂
  cases h₂
  case refl =>
    assumption
  case step h₃ =>
    rename_i n
    induction h₂ with
    | refl n =>
      apply le.step
      assumption
    | step m n h ih =>
      apply le.step
      apply ih
      assumption

def factorial1 : MyNat → MyNat :=
  rec one (λ n p => mul (succ n) p)

def factorial2 : (n : MyNat) → MyNat :=
  λ n => match n with
  | zero => one
  | succ n => mul (succ n) (factorial2 n)
