/-- The proof that the arithmetic mean of r₂ and r₃ is exactly the inradius r -/
theorem candidate (a b c r r₂ r₃ : ℝ)
    (hc : c ≠ 0)
    (h_pythagoras : a^2 + b^2 = c^2)
    (hr : r = (a + b - c) / 2)
    (hr₂ : r₂ = a - a^2 / c)
    (hr₃ : r₃ = b - b^2 / c) :
    (r₂ + r₃) / 2 = r :=
