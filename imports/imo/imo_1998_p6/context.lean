namespace IMO1998

/-- The functional equation, for functions of the positive integers into
themselves (modelled as `ℕ → ℕ` together with positivity hypotheses). -/
def Good (f : ℕ → ℕ) : Prop :=
  (∀ n, 0 < n → 0 < f n) ∧ ∀ s t, 0 < s → 0 < t → f (t ^ 2 * f s) = s * f t ^ 2

/-! ## The construction attaining the value `120` -/

/-- The involution of the primes swapping `2 ↔ 3` and `5 ↔ 37`. -/
def swapPrime (p : ℕ) : ℕ :=
  if p = 2 then 3 else if p = 3 then 2 else if p = 5 then 37 else if p = 37 then 5 else p

/-- The completely multiplicative extension of `swapPrime`. -/
def F (n : ℕ) : ℕ := n.factorization.prod fun p k => swapPrime p ^ k

section Lower

variable {f : ℕ → ℕ}

end Lower

section Normalized

variable {g : ℕ → ℕ}

end Normalized
