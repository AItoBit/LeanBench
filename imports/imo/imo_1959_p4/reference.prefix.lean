/-- Characterization: in any right triangle with hypotenuse `c` and legs `a, b`,
    the median to the hypotenuse `m = c / 2` satisfies `m^2 = a * b` if and only if
    `a^2 - 4 * a * b + b^2 = 0`. -/
theorem median_geom_mean_iff_quad_relation (a b c : ℝ) (h_pyth : a^2 + b^2 = c^2) :
    (c / 2)^2 = a * b ↔ a^2 - 4 * a * b + b^2 = 0 := by
  constructor
  · intro h
    have h1 : c^2 = 4 * (a * b) := by
      linarith [show (c / 2)^2 = c^2 / 4 by ring, h]
    linarith [h_pyth, h1]
  · intro h
    have h1 : c^2 = 4 * (a * b) := by
      linarith [h_pyth, h]
    calc
      (c / 2)^2 = c^2 / 4 := by ring
      _ = (4 * (a * b)) / 4 := by rw [h1]
      _ = a * b := by ring
