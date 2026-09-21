by
  -- Substitute the given definitions of the radii
  rw [hr, hr₂, hr₃]
  
  -- Group the terms algebraically over the common denominator c
  have h1 : a - a^2 / c + (b - b^2 / c) = a + b - (a^2 + b^2) / c := by ring
  
  calc (a - a^2 / c + (b - b^2 / c)) / 2
    _ = (a + b - (a^2 + b^2) / c) / 2 := by rw [h1]
    _ = (a + b - c^2 / c) / 2 := by rw [h_pythagoras]
    _ = (a + b - c) / 2 := by
      -- Simplify c^2 / c to c
      have h2 : c^2 / c = c := by
        calc c^2 / c = (c * c) / c := by rw [sq]
        _ = c := mul_div_cancel_right₀ c hc
      rw [h2]
