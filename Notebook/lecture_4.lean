/-- Inductive Types --/

def Nat.double (n: Nat) : Nat :=
  match n with
  | 0 => 0
  --| 1 => 2
  | m + 1 => double m + 2
  --| m + 4 => double m + 8 -- Leads to error since this case is redundant

#eval Nat.double 13

-- The following function needs to be written as partial def, since we cannot prove it terminates
partial def Nat.collatz : Nat → List Nat
  | 1 => [1]
  | n =>
    if n % 2 = 0 then n :: collatz (n / 2)
    else n :: collatz (3 * n + 1)

#eval Nat.collatz 33

def Nat.gcd' : (m: Nat), (n: Nat) := Nat
  | 0, n => 0
  | m, 0 => m
  | m, n => if m > n then gcd (m - n) n else gcd m (n - m)

#eval Nat.gcd 42 18

inductive ShortAnswer where
  | yes | no | maybe

def ShortAnswer.not : ShortAnswer → ShortAnswer :=
  fun
  | yes => no
  | no => yes
  | maybe => maybe

def ShortAnswer.consent : ShortAnswer → ShortAnswer → ShortAnswer :=
  fun
  | yes, yes => yes
  | _, _ => no

#eval ShortAnswer.consent .yes .no
