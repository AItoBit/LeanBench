by
  have ha' : a ≠ 0 := ne_of_gt ha
  have hb' : b ≠ 0 := ne_of_gt hb
  have hc' : c = 1 / (a * b) := by
    field_simp
    linear_combination habc
  -- the substitution `(x, y, z) = (a, 1, 1/b)`
  have hcore := core a 1 (1 / b) ha one_pos (by positivity)
  have key : (a - 1 + 1 / b) * (b - 1 + 1 / c) * (c - 1 + 1 / a)
      = (b / a) * ((a - 1 + 1 / b) * (1 - 1 / b + a) * (1 / b - a + 1)) := by
    rw [hc']
    field_simp
    ring
  rw [key]
  have hba : (0 : ℝ) < b / a := by positivity
  calc (b / a) * ((a - 1 + 1 / b) * (1 - 1 / b + a) * (1 / b - a + 1))
      ≤ (b / a) * (a * 1 * (1 / b)) := mul_le_mul_of_nonneg_left hcore hba.le
    _ = 1 := by field_simp
