by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2nn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  constructor
  · -- the bound holds
    intro a b c
    have hK : (0 : ℝ) ≤ 9 * Real.sqrt 2 / 32 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 := by positivity
    refine abs_le_of_sq_le_sq ?_ hK
    have hrw : (9 * Real.sqrt 2 / 32 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2) ^ 2
        = 81 / 512 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 4 := by
      linear_combination (81 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 4 / 1024) * hs2
    rw [hrw]
    linarith [core a b c]
  · -- and it is least
    intro M hM
    have h := hM (3 + Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2 - 3)
    have hE : (3 + Real.sqrt 2) * Real.sqrt 2 * ((3 + Real.sqrt 2) ^ 2 - Real.sqrt 2 ^ 2)
        + Real.sqrt 2 * (Real.sqrt 2 - 3) * (Real.sqrt 2 ^ 2 - (Real.sqrt 2 - 3) ^ 2)
        + (Real.sqrt 2 - 3) * (3 + Real.sqrt 2) * ((Real.sqrt 2 - 3) ^ 2 - (3 + Real.sqrt 2) ^ 2)
        = 162 * Real.sqrt 2 := by ring
    have hQ : (3 + Real.sqrt 2) ^ 2 + Real.sqrt 2 ^ 2 + (Real.sqrt 2 - 3) ^ 2 = 24 := by
      linear_combination 3 * hs2
    rw [hE, hQ, abs_of_nonneg (by positivity)] at h
    norm_num at h
    linarith
