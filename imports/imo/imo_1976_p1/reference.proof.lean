by
  have h16 : Real.sqrt 16 = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h64 : Real.sqrt 64 = 8 := by
    rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h128 : Real.sqrt 128 = 8 * Real.sqrt 2 := by
    rw [show (128 : ℝ) = 8 ^ 2 * 2 by norm_num, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num)]
  refine ⟨!₂[0, 4], !₂[0, 0], !₂[8, -4], !₂[8, 0], ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · norm_num [cross]
  · norm_num [cross]
  · norm_num [cross]
  · norm_num [cross]
  · norm_num [area]
  · norm_num [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, h16, h64]
  · norm_num [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, h128]
