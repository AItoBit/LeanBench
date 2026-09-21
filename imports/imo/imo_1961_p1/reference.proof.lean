by
  intro h
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2 := (h (-2) (Real.sqrt 2)).mpr (by rw [hsq]; norm_num)
  obtain ⟨x, hx, y, hy, z, hz, h1, -⟩ := h2
  linarith
