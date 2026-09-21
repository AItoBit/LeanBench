by
  dsimp [upperBound]
  -- Resolve the integer divisions for the even case
  have h1 : (2 * m) / 2 = m := by omega
  have h2 : (2 * m + 1) / 2 = m := by omega
  rw [h1, h2]
  -- Expand and simplify the resulting polynomial
  ring
