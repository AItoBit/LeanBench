/-- **IMO 1982, Problem 3 (b).**  The geometric sequence `(1/2)ⁱ` works. -/
theorem candidate :
    ∃ x : ℕ → ℝ, (∀ i, 0 < x i) ∧ x 0 = 1 ∧ (∀ i, x (i + 1) ≤ x i) ∧
      ∀ n : ℕ, ∑ i ∈ Finset.range n, (x i) ^ 2 / x (i + 1) < 4 :=
