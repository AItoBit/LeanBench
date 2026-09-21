namespace Imo1973P4

/-- The point of the plane with coordinates `(x, y)`, as a complex number. -/
noncomputable def pt (x y : ℝ) : ℂ := (x : ℂ) + (y : ℂ) * Complex.I
