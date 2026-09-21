by
  have h_sqrt_pos : 0 < sqrt an := by
    have h_pos : 0 < an := by linarith
    exact sqrt_pos.mpr h_pos
  have h_div_pos : 0 < 2 / sqrt an := by positivity
  linarith
