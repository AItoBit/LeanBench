by
  have hx : (0 : ℝ) ≤ s1 + s4 := by linarith
  have hy : (0 : ℝ) ≤ s2 + s5 := by linarith
  have hz : (0 : ℝ) ≤ s3 + s6 := by linarith
  -- clear the three denominators
  have e1 : ((s3 + s6) * w + (s1 + s4) * v) * (v * w) ≤ (4 * RA * u) * (v * w) :=
    mul_le_mul_of_nonneg_right hA (by positivity)
  have e2 : ((s2 + s5) * v + (s3 + s6) * u) * (u * v) ≤ (4 * RC * w) * (u * v) :=
    mul_le_mul_of_nonneg_right hC (by positivity)
  have e3 : ((s1 + s4) * u + (s2 + s5) * w) * (u * w) ≤ (4 * RE * v) * (u * w) :=
    mul_le_mul_of_nonneg_right hE (by positivity)
  -- the three AM-GM steps, in cleared form
  have g1 : (0 : ℝ) ≤ (s1 + s4) * w * (u - v) ^ 2 :=
    mul_nonneg (mul_nonneg hx hw.le) (sq_nonneg _)
  have g2 : (0 : ℝ) ≤ (s2 + s5) * u * (v - w) ^ 2 :=
    mul_nonneg (mul_nonneg hy hu.le) (sq_nonneg _)
  have g3 : (0 : ℝ) ≤ (s3 + s6) * v * (u - w) ^ 2 :=
    mul_nonneg (mul_nonneg hz hv.le) (sq_nonneg _)
  have huvw : (0 : ℝ) < u * v * w := by positivity
  have key : (2 * (s1 + s2 + s3 + s4 + s5 + s6)) * (u * v * w)
      ≤ (4 * (RA + RC + RE)) * (u * v * w) := by
    nlinarith [e1, e2, e3, g1, g2, g3]
  have hcancel : 2 * (s1 + s2 + s3 + s4 + s5 + s6) ≤ 4 * (RA + RC + RE) :=
    le_of_mul_le_mul_right key huvw
  linarith
