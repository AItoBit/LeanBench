by
  have hs0 : (0:ℝ) ≤ √31 := Real.sqrt_nonneg _
  have hs : (√31) ^ 2 = 31 := Real.sq_sqrt (by norm_num)
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_Ico]
  constructor
  · rintro ⟨h3, h1, h⟩
    exact ⟨by linarith, (Imo1962P2.key x h3 h1).1 h⟩
  · rintro ⟨hl, hr⟩
    have hsgt : (5:ℝ) < √31 := by nlinarith
    have h3 : (0:ℝ) ≤ 3 - x := by linarith
    have h1 : (0:ℝ) ≤ x + 1 := by linarith
    exact ⟨h3, h1, (Imo1962P2.key x h3 h1).2 hr⟩
