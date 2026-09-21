/-- The identity used to calculate the inradius r of the right triangle -/
lemma imo1969_p4_area_identity (a b c : ℝ) (h_pythagoras : a^2 + b^2 = c^2) :
    (a + b + c) * (a + b - c) = 2 * a * b := by
  calc (a + b + c) * (a + b - c)
    _ = a^2 + 2 * a * b + b^2 - c^2 := by ring
    _ = (a^2 + b^2) + 2 * a * b - c^2 := by ring
    _ = c^2 + 2 * a * b - c^2 := by rw [h_pythagoras]
    _ = 2 * a * b := by ring
