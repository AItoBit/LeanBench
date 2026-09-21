/-- For odd n = 2m + 1, the upper bound evaluates to m^2 + m - 2. -/
theorem upperBound_odd (m : ℤ) : upperBound (2 * m + 1) = m^2 + m - 2 := by
  dsimp [upperBound]
  -- Resolve the integer divisions for the odd case
  have h1 : (2 * m + 1) / 2 = m := by omega
  have h2 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
  rw [h1, h2]
  -- Expand and simplify the resulting polynomial
  ring
