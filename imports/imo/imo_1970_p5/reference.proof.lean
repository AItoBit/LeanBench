by
  
  -- 1. Establish the base inequality: (AB + BC + CA)^2 ≤ 3 * (AB^2 + BC^2 + CA^2)
  -- This is the algebraic equivalent of the Cauchy-Schwarz step used in the solution.
  have h_sq1 : 0 ≤ (AB - BC)^2 := sq_nonneg (AB - BC)
  have h_sq2 : 0 ≤ (BC - CA)^2 := sq_nonneg (BC - CA)
  have h_sq3 : 0 ≤ (CA - AB)^2 := sq_nonneg (CA - AB)
  
  have h_CS : (AB + BC + CA)^2 ≤ 3 * (AB^2 + BC^2 + CA^2) := by
    calc (AB + BC + CA)^2
      _ = 3 * (AB^2 + BC^2 + CA^2) - ((AB - BC)^2 + (BC - CA)^2 + (CA - AB)^2) := by ring
      _ ≤ 3 * (AB^2 + BC^2 + CA^2) - 0 := by linarith
      _ = 3 * (AB^2 + BC^2 + CA^2) := by ring

  -- 2. Substitute the geometric equality into the bound to yield the final result
  calc (AB + BC + CA)^2
    _ ≤ 3 * (AB^2 + BC^2 + CA^2) := h_CS
    _ = 3 * (2 * (DA^2 + DB^2 + DC^2)) := by rw [h_geom]
    _ = 6 * (DA^2 + DB^2 + DC^2) := by ring
