by
  subst hs
  subst hMx
  subst hMy
  subst hNx
  subst hNy
  have hspos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  -- the collinearity determinant is `√3 (3r² - 1)/2`
  have hkey : Real.sqrt 3 * (3 * r ^ 2 - 1) = 0 := by linear_combination 2 * hcol
  have h3r : 3 * r ^ 2 - 1 = 0 := by
    rcases mul_eq_zero.mp hkey with h | h
    · exact absurd h (ne_of_gt hspos)
    · exact h
  -- and `r > 0`
  have hfac : (r - Real.sqrt 3 / 3) * (r + Real.sqrt 3 / 3) = 0 := by
    linear_combination (1 / 3 : ℝ) * h3r - (1 / 9 : ℝ) * hs2
  rcases mul_eq_zero.mp hfac with h | h
  · linarith
  · linarith
