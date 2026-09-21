by
  refine ⟨fun i => (1 / 2 : ℝ) ^ i, ?_, ?_, ?_, ?_⟩
  · intro i; positivity
  · norm_num
  · intro i
    dsimp only
    have hp : (0 : ℝ) < (1 / 2 : ℝ) ^ i := by positivity
    rw [pow_succ]
    nlinarith
  · intro n
    dsimp only
    have hterm : ∀ i ∈ Finset.range n,
        ((1 / 2 : ℝ) ^ i) ^ 2 / (1 / 2 : ℝ) ^ (i + 1) = 2 * (1 / 2 : ℝ) ^ i := by
      intro i _
      have hp1 : ((1 / 2 : ℝ) ^ (i + 1)) ≠ 0 := by positivity
      rw [div_eq_iff hp1, sq, pow_succ]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
      geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1) n]
    have hval : 2 * (((1 / 2 : ℝ) ^ n - 1) / ((1 / 2 : ℝ) - 1))
        = 4 - 4 * (1 / 2 : ℝ) ^ n := by
      rw [show ((1 : ℝ) / 2 - 1) = -(1 / 2) from by norm_num]
      field_simp
      ring
    rw [hval]
    have hp : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
    linarith
