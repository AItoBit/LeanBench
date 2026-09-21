by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_Ico, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hx, hne, hlt⟩
    have ht : √(1 + 2 * x) ^ 2 = 1 + 2 * x := Real.sq_sqrt hx
    have hnn : 0 ≤ √(1 + 2 * x) := Real.sqrt_nonneg _
    rw [imo_1960_p2_div_eq x hx hne] at hlt
    refine ⟨⟨by linarith, by nlinarith⟩, ?_⟩
    rintro rfl
    apply hne
    norm_num
  · rintro ⟨⟨hlo, hhi⟩, hx0⟩
    have hx : 0 ≤ 1 + 2 * x := by linarith
    have ht : √(1 + 2 * x) ^ 2 = 1 + 2 * x := Real.sq_sqrt hx
    have hnn : 0 ≤ √(1 + 2 * x) := Real.sqrt_nonneg _
    have hne : (1 - √(1 + 2 * x)) ^ 2 ≠ 0 := by
      intro h
      have h0 : 1 - √(1 + 2 * x) = 0 := by
        have := sq_eq_zero_iff.mp h
        simpa using this
      have h1 : √(1 + 2 * x) = 1 := by linarith
      rw [h1] at ht
      exact hx0 (by linarith)
    refine ⟨hx, hne, ?_⟩
    rw [imo_1960_p2_div_eq x hx hne]
    have h7 : √(1 + 2 * x) < 7 / 2 := by nlinarith
    nlinarith
