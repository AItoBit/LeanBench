/-- Equal distances and equal squared distances are the same condition. -/
theorem sqrt_eq_iff (s w r : ℝ) :
    Real.sqrt ((s + r) ^ 2 + w ^ 2) = Real.sqrt ((s - r) ^ 2 + w ^ 2)
      ↔ (s + r) ^ 2 + w ^ 2 = (s - r) ^ 2 + w ^ 2 := by
  constructor
  · intro h
    have h1 : (0 : ℝ) ≤ (s + r) ^ 2 + w ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ (s - r) ^ 2 + w ^ 2 := by positivity
    rw [← Real.sq_sqrt h1, ← Real.sq_sqrt h2, h]
  · intro h; rw [h]
