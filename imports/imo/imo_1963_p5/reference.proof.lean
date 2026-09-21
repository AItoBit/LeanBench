by
  have h2 : Real.cos (2 * π / 7) = 2 * Real.cos (π / 7) ^ 2 - 1 := by
    have h : (2 : ℝ) * π / 7 = 2 * (π / 7) := by ring
    rw [h, Real.cos_two_mul]
  have h3 : Real.cos (3 * π / 7) = 4 * Real.cos (π / 7) ^ 3 - 3 * Real.cos (π / 7) := by
    have h : (3 : ℝ) * π / 7 = 3 * (π / 7) := by ring
    rw [h, Real.cos_three_mul]
  rw [h2, h3]
  have := cos_pi_div_seven_cubic
  linarith
