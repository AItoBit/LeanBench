namespace Imo1972P4

/-- From `a² * b² = 0` with `a > 0` we get `b = 0`. -/
private lemma eq_zero_of_sq_mul_sq {a b : ℝ} (ha : 0 < a) (h : a ^ 2 * b ^ 2 = 0) : b = 0 := by
  rcases mul_eq_zero.mp h with h' | h'
  · exact absurd h' (pow_ne_zero 2 ha.ne')
  · exact sq_eq_zero_iff.mp h'

/-- The algebraic identity behind the solution: twice the sum of the five
left-hand sides is a sum of ten squares. -/
private lemma key (x₁ x₂ x₃ x₄ x₅ : ℝ) :
    x₁ ^ 2 * (x₂ - x₄) ^ 2 + x₂ ^ 2 * (x₃ - x₅) ^ 2 + x₃ ^ 2 * (x₄ - x₁) ^ 2
      + x₄ ^ 2 * (x₅ - x₂) ^ 2 + x₅ ^ 2 * (x₁ - x₃) ^ 2
      + x₁ ^ 2 * (x₃ - x₅) ^ 2 + x₂ ^ 2 * (x₄ - x₁) ^ 2 + x₃ ^ 2 * (x₅ - x₂) ^ 2
      + x₄ ^ 2 * (x₁ - x₃) ^ 2 + x₅ ^ 2 * (x₂ - x₄) ^ 2
    = 2 * ((x₁ ^ 2 - x₃ * x₅) * (x₂ ^ 2 - x₃ * x₅)
         + (x₂ ^ 2 - x₄ * x₁) * (x₃ ^ 2 - x₄ * x₁)
         + (x₃ ^ 2 - x₅ * x₂) * (x₄ ^ 2 - x₅ * x₂)
         + (x₄ ^ 2 - x₁ * x₃) * (x₅ ^ 2 - x₁ * x₃)
         + (x₅ ^ 2 - x₂ * x₄) * (x₁ ^ 2 - x₂ * x₄)) := by
  ring
