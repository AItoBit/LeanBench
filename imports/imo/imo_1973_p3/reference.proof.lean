by
  constructor
  · -- `a = 4/5`, `b = -2/5`, root `x = -1`
    exact ⟨4 / 5, -2 / 5, ⟨-1, by norm_num⟩, by norm_num⟩
  · rintro y ⟨a, b, ⟨x, hx⟩, rfl⟩
    -- `x ≠ 0`
    have hx0 : x ≠ 0 := by
      intro h
      rw [h] at hx
      norm_num at hx
    have hx2 : 0 < x ^ 2 := by
      rcases lt_trichotomy x 0 with h | h | h
      · nlinarith
      · exact absurd h hx0
      · nlinarith
    have hx4 : 0 < x ^ 4 := by nlinarith [mul_pos hx2 hx2]
    have hP : 0 < x ^ 2 * (x ^ 2 + 1) ^ 2 + x ^ 4 := by
      have h1 : (0:ℝ) ≤ x ^ 2 * (x ^ 2 + 1) ^ 2 := by positivity
      linarith
    -- the equation, rewritten as a scalar product
    have heq : a * ((x ^ 2 + 1) * x) + b * x ^ 2 = -(x ^ 4 + 1) := by linear_combination hx
    -- Cauchy–Schwarz
    have hCS : (a * ((x ^ 2 + 1) * x) + b * x ^ 2) ^ 2
        ≤ (a ^ 2 + b ^ 2) * (x ^ 2 * (x ^ 2 + 1) ^ 2 + x ^ 4) := by
      nlinarith [sq_nonneg (a * x ^ 2 - b * ((x ^ 2 + 1) * x))]
    rw [heq] at hCS
    -- the polynomial inequality `(x⁴+1)² ≥ (4/5) P`
    have hkey : (4 / 5) * (x ^ 2 * (x ^ 2 + 1) ^ 2 + x ^ 4) ≤ (x ^ 4 + 1) ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg (x ^ 2 - 1))
        (by positivity : (0:ℝ) ≤ 5 * x ^ 4 + 6 * x ^ 2 + 5)]
    -- divide by `P > 0`
    exact le_of_mul_le_mul_right (by nlinarith [hCS, hkey]) hP
