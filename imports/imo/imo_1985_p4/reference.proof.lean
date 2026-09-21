by
  calc a * b * c * d = (a * b) * (c * d) := by ring
    _ = x^2 * y^2 := by rw [hx, hy]
    _ = (x * y)^2 := by ring
    _ = (z^2)^2 := by rw [hz]
    _ = z^4 := by ring
