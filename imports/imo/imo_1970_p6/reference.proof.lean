by
  
  -- Substitute the definitions of L1 and L2 into the ratio inequality
  -- and rearrange the terms to isolate the positive scalar k.
  have h_scaled : k * (10 * A) ≤ k * (7 * T) := by
    calc k * (10 * A)
      _ = 10 * (k * A) := by ring
      _ = 10 * L2 := by rw [← hL2]
      _ ≤ 7 * L1 := h_ratio
      _ = 7 * (k * T) := by rw [hL1]
      _ = k * (7 * T) := by ring

  -- Cancel the strictly positive overcounting factor k 
  -- to conclude the final bounds between A and T.
  exact Nat.le_of_mul_le_mul_left h_scaled hk_pos
