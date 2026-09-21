by
  
  -- Establish that n / n = 1 for the non-zero number of sides
  have h_div : n / n = 1 := div_self hn
  
  -- Verify the summation of the opposite angles algebraically
  calc angle_YBZ + angle_YXZ = (n - 2) * Real.pi / n + 2 * Real.pi / n := by rw [h_YBZ, h_YXZ]
    _ = Real.pi * (n / n) := by ring
    _ = Real.pi * 1 := by rw [h_div]
    _ = Real.pi := by ring
