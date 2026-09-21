namespace IMO2015P2

/-!
# IMO 2015 Problem 2

Determine all positive integers `(a,b,c)` such that

    a*b - c
    b*c - a
    c*a - b

are powers of two.

We work over `ℤ` so that subtraction has its ordinary
integer meaning.
-/

/-!
## Powers of two
-/

def IsPowerOfTwo (z : ℤ) : Prop :=
  ∃ m : ℕ, z = 2 ^ m

def Good
    (a b c : ℤ) : Prop :=
  0 < a ∧
  0 < b ∧
  0 < c ∧
  IsPowerOfTwo (a * b - c) ∧
  IsPowerOfTwo (b * c - a) ∧
  IsPowerOfTwo (c * a - b)

/-!
## Symmetry
-/

def IsListed
    (a b c : ℤ) : Prop :=
  (a = 2 ∧ b = 2 ∧ c = 2) ∨
  (a = 2 ∧ b = 2 ∧ c = 3) ∨
  (a = 2 ∧ b = 3 ∧ c = 2) ∨
  (a = 3 ∧ b = 2 ∧ c = 2) ∨
  (a = 2 ∧ b = 6 ∧ c = 11) ∨
  (a = 6 ∧ b = 11 ∧ c = 2) ∨
  (a = 11 ∧ b = 2 ∧ c = 6) ∨
  (a = 6 ∧ b = 2 ∧ c = 11) ∨
  (a = 2 ∧ b = 11 ∧ c = 6) ∨
  (a = 11 ∧ b = 6 ∧ c = 2) ∨
  (a = 3 ∧ b = 5 ∧ c = 7) ∨
  (a = 5 ∧ b = 7 ∧ c = 3) ∨
  (a = 7 ∧ b = 3 ∧ c = 5) ∨
  (a = 5 ∧ b = 3 ∧ c = 7) ∨
  (a = 3 ∧ b = 7 ∧ c = 5) ∨
  (a = 7 ∧ b = 5 ∧ c = 3)
