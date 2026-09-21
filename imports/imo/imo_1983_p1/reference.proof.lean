by
  refine ⟨fun x hx => by positivity, fun x y hx hy => by field_simp, ?_⟩
  simpa [one_div] using tendsto_inv_atTop_zero
