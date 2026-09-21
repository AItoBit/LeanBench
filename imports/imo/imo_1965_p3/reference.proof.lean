by
  rw [volLower_formula hk, volUpper_formula hk]
  have hk1 : (k + 1) ^ 3 ≠ 0 := by positivity
  have hV_ne : V ≠ 0 := ne_of_gt hV
  have hDen : (3 * k + 1) ≠ 0 := by positivity
  have : (k ^ 3 + 3 * k ^ 2) / (k + 1) ^ 3 * V / ((3 * k + 1) / (k + 1) ^ 3 * V)
       = (k ^ 3 + 3 * k ^ 2) / (3 * k + 1) := by
    field_simp
  rw [this]
  congr 1
  ring
