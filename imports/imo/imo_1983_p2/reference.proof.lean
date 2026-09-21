by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h15 : Real.sqrt 15 ^ 2 = 15 := Real.sq_sqrt (by norm_num)
  have h3pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨mkP 0 0, mkP 2 0, mkP (7/4) (Real.sqrt 15/4), mkP 1 (Real.sqrt 3),
    mkP (5/2) (Real.sqrt 3/2), mkP 1 (-Real.sqrt 3), mkP (5/2) (-(Real.sqrt 3)/2),
    mkP 1 0, mkP (5/2) 0, 2, 1, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [dist_eq_norm, mkP_sub, mkP_norm,
      show (7/4-0:ℝ)^2 + (Real.sqrt 15/4 - 0)^2 = 2^2 by
        rw [show (Real.sqrt 15/4-0) = Real.sqrt 15/4 by ring, div_pow, h15]; norm_num]
    exact Real.sqrt_sq (by norm_num)
  · rw [dist_eq_norm, mkP_sub, mkP_norm,
      show (7/4-2:ℝ)^2 + (Real.sqrt 15/4 - 0)^2 = 1^2 by
        rw [show (Real.sqrt 15/4-0) = Real.sqrt 15/4 by ring, div_pow, h15]; norm_num]
    exact Real.sqrt_sq (by norm_num)
  · rw [dist_eq_norm, mkP_sub, mkP_norm,
      show (1-0:ℝ)^2 + (Real.sqrt 3 - 0)^2 = 2^2 by
        rw [show (Real.sqrt 3-0) = Real.sqrt 3 by ring, h3]; norm_num]
    exact Real.sqrt_sq (by norm_num)
  · rw [dist_eq_norm, mkP_sub, mkP_norm,
      show (5/2-2:ℝ)^2 + (Real.sqrt 3/2 - 0)^2 = 1^2 by
        rw [show (Real.sqrt 3/2-0) = Real.sqrt 3/2 by ring, div_pow, h3]; norm_num]
    exact Real.sqrt_sq (by norm_num)
  · rw [dist_eq_norm, mkP_sub, mkP_norm,
      show (1-0:ℝ)^2 + (-Real.sqrt 3 - 0)^2 = 2^2 by
        rw [show (-Real.sqrt 3-0) = -Real.sqrt 3 by ring, neg_pow, h3]; norm_num]
    exact Real.sqrt_sq (by norm_num)
  · rw [dist_eq_norm, mkP_sub, mkP_norm,
      show (5/2-2:ℝ)^2 + (-(Real.sqrt 3)/2 - 0)^2 = 1^2 by
        rw [show (-(Real.sqrt 3)/2-0) = -(Real.sqrt 3)/2 by ring, div_pow, neg_pow, h3]
        norm_num]
    exact Real.sqrt_sq (by norm_num)
  · exact mkP_ne_of_fst _ _ _ _ (by norm_num)
  · rw [mkP_sub, mkP_sub, mkP_inner]; nlinarith [h3]
  · rw [mkP_sub, mkP_sub, mkP_inner]; nlinarith [h3]
  · exact mkP_ne_of_fst _ _ _ _ (by norm_num)
  · rw [mkP_sub, mkP_sub, mkP_inner]; nlinarith [h3]
  · rw [mkP_sub, mkP_sub, mkP_inner]; nlinarith [h3]
  · exact mkP_ne_of_snd _ _ _ _ (by intro h; nlinarith [h3pos])
  · rw [mkP_midpoint]; norm_num
  · rw [mkP_midpoint, show (Real.sqrt 3 / 2 + -Real.sqrt 3 / 2) / 2 = 0 by ring]; norm_num
