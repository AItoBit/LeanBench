/-- The key inequality, by Ravi substitution and AM–GM. -/
theorem three_le_sum_div (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hu : 0 < b + c - a) (hv : 0 < c + a - b) (hw : 0 < a + b - c) :
    3 ≤ a / (b + c - a) + b / (c + a - b) + c / (a + b - c) := by
  rw [div_add_div _ _ hu.ne' hv.ne', div_add_div _ _ (by positivity) hw.ne',
    le_div_iff₀ (by positivity)]
  nlinarith [mul_nonneg hu.le (sq_nonneg (b - c)), mul_nonneg hv.le (sq_nonneg (c - a)),
    mul_nonneg hw.le (sq_nonneg (a - b))]

/-- `[A₀B₀C₀] = 2 · [AC₁BA₁CB₁]`. -/
theorem excentralArea_eq_two_mul_hexArea
    (hu : 0 < b + c - a) (hv : 0 < c + a - b) (hw : 0 < a + b - c)
    (hS : S = r * (a + b + c) / 2) :
    excentralArea a b c r S = 2 * hexArea a b c r S := by
  simp only [excentralArea, hexArea, hS]
  field_simp
  ring

/-- `4 · [ABC] ≤ [A₀B₀C₀]`. -/
theorem four_mul_le_excentralArea
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hr : 0 < r)
    (hu : 0 < b + c - a) (hv : 0 < c + a - b) (hw : 0 < a + b - c)
    (hS : S = r * (a + b + c) / 2) :
    4 * S ≤ excentralArea a b c r S := by
  have hkey := three_le_sum_div ha hb hc hu hv hw
  have hp : 0 < r * (a + b + c) / 2 := by positivity
  have hrw : excentralArea a b c r S - 4 * S
      = (r * (a + b + c) / 2) *
        (a / (b + c - a) + b / (c + a - b) + c / (a + b - c) - 3) := by
    simp only [excentralArea, hS]
    field_simp
    ring
  nlinarith [mul_nonneg hp.le (by linarith : (0 : ℝ) ≤
    a / (b + c - a) + b / (c + a - b) + c / (a + b - c) - 3)]
