by
  have key : Real.sqrt (7 / 3) * Real.sqrt 3 = Real.sqrt 7 := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 7 / 3)]
    norm_num
  linear_combination (-(s / 2)) * key
