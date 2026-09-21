/-- Auxiliary: forward direction. If `x` solves the equation, then `0 ≤ p ≤ 4/3`
and `x` is the claimed root. -/
theorem imo_1963_p1_forward (p x : ℝ) (h1 : 0 ≤ x ^ 2 - p) (h2 : 0 ≤ x ^ 2 - 1)
    (heq : √(x ^ 2 - p) + 2 * √(x ^ 2 - 1) = x) :
    0 ≤ p ∧ p ≤ 4 / 3 ∧ x = (4 - p) / (2 * √(4 - 2 * p)) := by
  set a : ℝ := √(x ^ 2 - p)
  set b : ℝ := √(x ^ 2 - 1)
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = x ^ 2 - p := Real.sq_sqrt h1
  have hb2 : b ^ 2 = x ^ 2 - 1 := Real.sq_sqrt h2
  have hx0 : 0 ≤ x := by rw [← heq]; positivity
  have hx1 : 1 ≤ x ^ 2 := by linarith
  -- squaring once: `4ab = 4 + p - 4x²`
  have hab : 4 * (a * b) = 4 + p - 4 * x ^ 2 := by
    linear_combination (a + 2 * b + x) * heq - ha2 - 4 * hb2
  have habnn : 0 ≤ 4 + p - 4 * x ^ 2 := by nlinarith [mul_nonneg ha0 hb0]
  -- squaring twice
  have hsq : 16 * ((x ^ 2 - p) * (x ^ 2 - 1)) = (4 + p - 4 * x ^ 2) ^ 2 := by
    rw [← ha2, ← hb2]
    linear_combination (4 * (a * b) + (4 + p - 4 * x ^ 2)) * hab
  have hkey : x ^ 2 * (16 - 8 * p) = (4 - p) ^ 2 := by linear_combination hsq
  have hp2 : p < 2 := by
    by_contra hc
    have hple : 2 ≤ p := not_lt.mp hc
    nlinarith [mul_nonneg (sub_nonneg.mpr hx1) (show (0:ℝ) ≤ 8 * p - 16 by linarith)]
  have hmul : 0 ≤ (4 + p - 4 * x ^ 2) * (16 - 8 * p) :=
    mul_nonneg habnn (by linarith)
  have hp0 : 0 ≤ p := by nlinarith
  have hp1 : p ≤ 4 / 3 := by nlinarith
  refine ⟨hp0, hp1, ?_⟩
  set s : ℝ := √(4 - 2 * p)
  have hs2 : s ^ 2 = 4 - 2 * p := Real.sq_sqrt (by linarith)
  have hspos : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hsnn : 0 ≤ 2 * x * s := by positivity
  have hpnn : 0 ≤ 4 - p := by linarith
  have hfac : (2 * x * s - (4 - p)) * (2 * x * s + (4 - p)) = 0 := by
    linear_combination (4 * x ^ 2) * hs2 + hkey
  have hxs : 2 * x * s = 4 - p := by
    rcases mul_eq_zero.mp hfac with h | h
    · linarith
    · linarith
  field_simp
  linear_combination hxs

/-- Auxiliary: backward direction. -/
theorem imo_1963_p1_backward (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 4 / 3) :
    ∀ x : ℝ, x = (4 - p) / (2 * √(4 - 2 * p)) →
      0 ≤ x ^ 2 - p ∧ 0 ≤ x ^ 2 - 1 ∧ √(x ^ 2 - p) + 2 * √(x ^ 2 - 1) = x := by
  intro x hx
  set s : ℝ := √(4 - 2 * p)
  have hs2 : s ^ 2 = 4 - 2 * p := Real.sq_sqrt (by linarith)
  have hspos : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have e1 : x ^ 2 - p = ((4 - 3 * p) / (2 * s)) ^ 2 := by
    rw [hx]
    field_simp
    linear_combination (-4 * p) * hs2
  have e2 : x ^ 2 - 1 = (p / (2 * s)) ^ 2 := by
    rw [hx]
    field_simp
    linear_combination (-4 : ℝ) * hs2
  have hnn1 : (0:ℝ) ≤ (4 - 3 * p) / (2 * s) :=
    div_nonneg (by linarith) (by positivity)
  have hnn2 : (0:ℝ) ≤ p / (2 * s) := by positivity
  refine ⟨by rw [e1]; positivity, by rw [e2]; positivity, ?_⟩
  rw [e1, e2, Real.sqrt_sq hnn1, Real.sqrt_sq hnn2, hx]
  field_simp
  ring
