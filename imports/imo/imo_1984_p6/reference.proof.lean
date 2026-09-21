by
  
  -- Substitute h_sum into the LHS of h_prod
  have h1 : (b - a) * P_m1 = b * (2 * P_m1) - a * (P_m1 * P_km1) := by
    calc (b - a) * P_m1 = (b - a) * (b + a) := by rw [h_sum]
      _ = b * (2 * P_m1) - a * (P_m1 * P_km1) := h_prod
      
  -- Rearrange h1 to factor out P_m1 on the RHS
  have h2 : (b - a) * P_m1 = (2 * b - a * P_km1) * P_m1 := by
    calc (b - a) * P_m1 = b * (2 * P_m1) - a * (P_m1 * P_km1) := h1
      _ = (2 * b - a * P_km1) * P_m1 := by ring
      
  -- Cancel P_m1 from both sides (requires P_m1 ≠ 0)
  have h3 : b - a = 2 * b - a * P_km1 := mul_right_cancel₀ h_Pm1_pos h2
  
  -- The remaining equations form a simple linear system:
  -- 1) b - a = 2b - a * P_km1
  -- 2) b + a = P_m1
  -- We solve this to find a * P_km1 = P_m1
  have h4 : b = a * P_km1 - a := by linarith
  
  calc a * P_km1 = (a * P_km1 - a) + a := by ring
    _ = b + a := by rw [h4]
    _ = P_m1 := h_sum
