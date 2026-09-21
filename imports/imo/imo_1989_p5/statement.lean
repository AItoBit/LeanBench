/-- **IMO 1989 P5.** -/
theorem candidate (n : ℕ) (hn : 0 < n) :
    ∃ m : ℕ, 0 < m ∧ ∀ i < n, ¬ IsPrimePow (m + i) :=
