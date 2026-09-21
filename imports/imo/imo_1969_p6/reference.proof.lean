by
  have h : (x + x) * (y + y) - (z + z) ^ 2 = 4 * (x * y - z ^ 2) := by ring
  rw [h]
  field_simp
  ring
