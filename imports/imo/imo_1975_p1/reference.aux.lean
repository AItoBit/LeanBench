/-- Two antitone (non-increasing) real sequences monovary. -/
theorem monovary_of_antitone {n : ℕ} {x y : Fin n → ℝ} (hx : Antitone x) (hy : Antitone y) :
    Monovary x y := by
  intro i j hij
  rcases le_total i j with h | h
  · exact absurd (hy h) (not_le.2 hij)
  · exact hx h

/-- Rearrangement step: for antitone `x`, `y` and any permutation `σ`,
the sum `∑ x i * y (σ i)` is maximal at `σ = id`. -/
theorem sum_mul_comp_perm_le {n : ℕ} {x y : Fin n → ℝ} (hx : Antitone x) (hy : Antitone y)
    (σ : Equiv.Perm (Fin n)) : ∑ i, x i * y (σ i) ≤ ∑ i, x i * y i := by
  simpa [smul_eq_mul] using
    (monovary_of_antitone hx hy).sum_smul_comp_perm_le_sum_smul (σ := σ)
