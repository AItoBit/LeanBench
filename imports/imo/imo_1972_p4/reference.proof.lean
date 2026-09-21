by
  constructor
  · rintro ⟨e₁, e₂, e₃, e₄, e₅⟩
    -- the sum of the ten squares is `≤ 0`
    have hsum : x₁ ^ 2 * (x₂ - x₄) ^ 2 + x₂ ^ 2 * (x₃ - x₅) ^ 2 + x₃ ^ 2 * (x₄ - x₁) ^ 2
        + x₄ ^ 2 * (x₅ - x₂) ^ 2 + x₅ ^ 2 * (x₁ - x₃) ^ 2
        + x₁ ^ 2 * (x₃ - x₅) ^ 2 + x₂ ^ 2 * (x₄ - x₁) ^ 2 + x₃ ^ 2 * (x₅ - x₂) ^ 2
        + x₄ ^ 2 * (x₁ - x₃) ^ 2 + x₅ ^ 2 * (x₂ - x₄) ^ 2 ≤ 0 := by
      rw [key]
      linarith
    -- every summand is nonnegative
    have n1 : (0:ℝ) ≤ x₁ ^ 2 * (x₂ - x₄) ^ 2 := by positivity
    have n2 : (0:ℝ) ≤ x₂ ^ 2 * (x₃ - x₅) ^ 2 := by positivity
    have n3 : (0:ℝ) ≤ x₃ ^ 2 * (x₄ - x₁) ^ 2 := by positivity
    have n4 : (0:ℝ) ≤ x₄ ^ 2 * (x₅ - x₂) ^ 2 := by positivity
    have n5 : (0:ℝ) ≤ x₅ ^ 2 * (x₁ - x₃) ^ 2 := by positivity
    have n6 : (0:ℝ) ≤ x₁ ^ 2 * (x₃ - x₅) ^ 2 := by positivity
    have n7 : (0:ℝ) ≤ x₂ ^ 2 * (x₄ - x₁) ^ 2 := by positivity
    have n8 : (0:ℝ) ≤ x₃ ^ 2 * (x₅ - x₂) ^ 2 := by positivity
    have n9 : (0:ℝ) ≤ x₄ ^ 2 * (x₁ - x₃) ^ 2 := by positivity
    have n10 : (0:ℝ) ≤ x₅ ^ 2 * (x₂ - x₄) ^ 2 := by positivity
    -- hence each of them vanishes
    have z1 : x₁ ^ 2 * (x₂ - x₄) ^ 2 = 0 := by linarith
    have z2 : x₂ ^ 2 * (x₃ - x₅) ^ 2 = 0 := by linarith
    have z3 : x₃ ^ 2 * (x₄ - x₁) ^ 2 = 0 := by linarith
    have z4 : x₄ ^ 2 * (x₅ - x₂) ^ 2 = 0 := by linarith
    have d1 : x₂ - x₄ = 0 := eq_zero_of_sq_mul_sq h₁ z1
    have d2 : x₃ - x₅ = 0 := eq_zero_of_sq_mul_sq h₂ z2
    have d3 : x₄ - x₁ = 0 := eq_zero_of_sq_mul_sq h₃ z3
    have d4 : x₅ - x₂ = 0 := eq_zero_of_sq_mul_sq h₄ z4
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg x₁]
