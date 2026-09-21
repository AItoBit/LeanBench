/-- The quadratic `y^2 + y - 1 = 0` holds exactly for the two values `(-1 ± √5)/2`. -/
theorem imo_1963_p4_quadratic_iff (y : ℝ) :
    y ^ 2 + y - 1 = 0 ↔ y = (-1 + √5) / 2 ∨ y = (-1 - √5) / 2 := by
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  constructor
  · intro h
    have hfac : (y - (-1 + √5) / 2) * (y - (-1 - √5) / 2) = 0 := by
      have hexp : (y - (-1 + √5) / 2) * (y - (-1 - √5) / 2)
          = y ^ 2 + y - 1 + (5 - √5 ^ 2) / 4 := by ring
      rw [hexp, h, h5]; ring
    rcases mul_eq_zero.mp hfac with h' | h'
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> nlinarith [h5]
