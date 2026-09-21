namespace GoldenRatioFunction

/-- The golden ratio. -/
noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

/-- The required function, defined by nearest-integer rounding of `phi * n`. -/
noncomputable def goldenFunction (n : ℕ) : ℕ :=
  ⌊phi * (n : ℝ) + 1 / 2⌋₊
