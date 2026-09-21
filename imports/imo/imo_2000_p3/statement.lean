/-- **IMO 2000 P3.** The points can be driven arbitrarily far to the right exactly when
`k ≥ 1/(N-1)`. -/
theorem candidate (N : ℕ) (hN : 2 ≤ N) (k : ℝ) (hk : 0 < k) :
    (∀ x : Fin N → ℝ, (∃ i j, x i ≠ x j) → ∀ M : ℝ, ∃ y, Reach k x y ∧ ∀ i, M < y i)
      ↔ 1 / ((N : ℝ) - 1) ≤ k :=
