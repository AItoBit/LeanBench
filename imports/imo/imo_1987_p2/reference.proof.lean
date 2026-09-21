by
  
  -- Step 1: Cross-multiply the similarity ratio
  have h_cross : KM * AN = BC * AL := by
    -- Multiply both sides by BC and AN
    calc KM * AN = (KM / BC) * BC * AN := by
           rw [div_mul_cancel₀ _ h_BC_pos]
         _ = (AL / AN) * BC * AN := by rw [h_ratio]
         _ = (AL / AN) * AN * BC := by ring
         _ = AL * BC := by rw [div_mul_cancel₀ _ h_AN_pos]
         _ = BC * AL := by ring

  -- Step 2: Substitute the cross-multiplied identity into the area formulas
  calc Area_AKNM = (1 / 2) * (KM * AN) := by
         have h_assoc : (1 / 2 : ℝ) * KM * AN = (1 / 2 : ℝ) * (KM * AN) := by ring
         rw [h_area_quad, h_assoc]
       _ = (1 / 2) * (BC * AL) := by rw [h_cross]
       _ = (1 / 2) * BC * AL := by ring
       _ = Area_ABC := h_area_tri.symm
