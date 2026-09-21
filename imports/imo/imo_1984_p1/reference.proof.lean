by
  rw [target_eq_quarter_mul_add_quarter x y z hsum]
  have h_amgm := prod_le_one_twenty_seventh x y z hx hy hz hsum
  have h_bound : (1 / 4 : ℝ) * ((1 - 2 * x) * (1 - 2 * y) * (1 - 2 * z)) + 1 / 4 ≤
      (1 / 4) * (1 / 27) + 1 / 4 := by
    linarith
  have h_calc : (1 / 4 : ℝ) * (1 / 27) + 1 / 4 = 7 / 27 := by norm_num
  rwa [h_calc] at h_bound
