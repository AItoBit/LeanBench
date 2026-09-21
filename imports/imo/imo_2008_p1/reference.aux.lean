/-- The computation behind the whole problem. -/
theorem key (a1 a2 b1 b2 c1 c2 R t : ℝ)
    (hA : a1 ^ 2 + a2 ^ 2 = R ^ 2) (hB : b1 ^ 2 + b2 ^ 2 = R ^ 2)
    (hC : c1 ^ 2 + c2 ^ 2 = R ^ 2)
    (hdist : (t * (c1 - b1)) ^ 2 + (t * (c2 - b2)) ^ 2
      = ((b1 + c1) / 2 - (a1 + b1 + c1)) ^ 2 + ((b2 + c2) / 2 - (a2 + b2 + c2)) ^ 2) :
    ((b1 + c1) / 2 + t * (c1 - b1)) ^ 2 + ((b2 + c2) / 2 + t * (c2 - b2)) ^ 2
      = 2 * R ^ 2 + (a1 * b1 + a2 * b2) + (b1 * c1 + b2 * c2) + (c1 * a1 + c2 * a2) := by
  linear_combination hA + (1 / 2 - t) * hB + (1 / 2 + t) * hC + hdist
