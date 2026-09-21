namespace IMO2001P4

open Equiv Finset

open scoped Nat

variable {n : ℕ} {c : Fin n → ℤ}

/-- The function `S` in the problem. As implemented here it accepts a permutation of `Fin n`
rather than `Icc 1 n`, and as such contains `+ 1` to compensate. -/
def S (c : Fin n → ℤ) (a : Perm (Fin n)) : ℤ := ∑ i, c i * (a i + 1)
