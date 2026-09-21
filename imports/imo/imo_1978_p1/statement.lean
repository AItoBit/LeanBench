/-- **IMO 1978, Problem 1.** -/
theorem candidate :
    IsLeast {s : ℕ | ∃ m n : ℕ, 1 ≤ m ∧ m < n ∧
      1978 ^ m % 1000 = 1978 ^ n % 1000 ∧ s = m + n} 106 :=
