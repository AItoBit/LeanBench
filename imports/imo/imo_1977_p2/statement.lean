/-- **IMO 1977, Problem 2.** -/
theorem candidate :
    IsGreatest {n : ℕ | ∃ x : ℕ → ℝ,
      (∀ i, i + 7 ≤ n → (∑ j ∈ Finset.range 7, x (i + j)) < 0) ∧
      (∀ i, i + 11 ≤ n → 0 < ∑ j ∈ Finset.range 11, x (i + j))} 16 :=
