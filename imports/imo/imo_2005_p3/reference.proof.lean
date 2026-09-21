by
  have hs : (0 : ℝ) < x ^ 2 + y ^ 2 + z ^ 2 := by positivity
  have hbx := term_bound x y z hx hy hz
  have hby := term_bound y x z hy hx hz
  have hbz := term_bound z x y hz hx hy
  have ey : (x ^ 2 + y ^ 5 + z ^ 2) = y ^ 5 + x ^ 2 + z ^ 2 := by ring
  have ez : (x ^ 2 + y ^ 2 + z ^ 5) = z ^ 5 + x ^ 2 + y ^ 2 := by ring
  have esy : (y ^ 2 + x ^ 2 + z ^ 2) = x ^ 2 + y ^ 2 + z ^ 2 := by ring
  have esz : (z ^ 2 + x ^ 2 + y ^ 2) = x ^ 2 + y ^ 2 + z ^ 2 := by ring
  rw [ey, ez]
  rw [esy] at hby
  rw [esz] at hbz
  -- the three lower bounds add up to `1 - (1/x + 1/y + 1/z)/(x² + y² + z²)`
  have hsum : (1 / x + y ^ 2 + z ^ 2) / (x ^ 2 + y ^ 2 + z ^ 2)
      + (1 / y + x ^ 2 + z ^ 2) / (x ^ 2 + y ^ 2 + z ^ 2)
      + (1 / z + x ^ 2 + y ^ 2) / (x ^ 2 + y ^ 2 + z ^ 2)
      = (1 / x + 1 / y + 1 / z) / (x ^ 2 + y ^ 2 + z ^ 2) + 2 := by
    field_simp
    ring
  have hfin : (1 / x + 1 / y + 1 / z) / (x ^ 2 + y ^ 2 + z ^ 2) ≤ 1 := by
    rw [div_le_one hs]
    exact inv_sum_le_sq_sum x y z hx hy hz h
  linarith
