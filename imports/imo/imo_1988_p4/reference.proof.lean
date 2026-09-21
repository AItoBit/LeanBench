by
  
  -- Substitute the given definitions into the length formula
  calc sum_r - sum_k = (-a_69 / a_70) - sum_k := by rw [h_vieta]
    _ = (- (-5 * sum_k - 4 * sum_k) / 5) - sum_k := by rw [h_a69, h_a70]
    
    -- Simplify the algebraic expression
    _ = (9 * sum_k / 5) - sum_k := by ring
    
    -- Substitute the arithmetic value of the sum and evaluate
    _ = (9 * (35 * 71) / 5) - (35 * 71) := by rw [h_sum_k]
    _ = 1988 := by norm_num
