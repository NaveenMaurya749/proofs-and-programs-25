import Mathlib

def factorial' :=
  Nat.rec (motive := fun _ => Nat) 1 (fun n f => (n+1)*f)

#eval factorial' 52

def parity : Nat → Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun _n f => !f)

theorem factorial_zero : factorial' 0 = 1 := rfl

theorem factorial_succ (n : Nat) :
  factorial' (n+1) = (n+1)*factorial' n := rfl

theorem Nat.recFromzero {α : Type u}
    (zeroData : α) (stepData : Nat → α → α) (n : Nat) :
  Nat.rec zeroData stepData (n + 1) = stepData n (Nat.rec zeroData stepData n)
  := rfl

#check (1, (2, 3))
#check ((1, 2), 3)

def Tuple : (n : Nat) → Type
  | 0 => Unit
  | n + 1 => Nat ⨯ Tuple n
