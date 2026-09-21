/-- The two closed forms of the answer agree: with `h = (√3/2) s`,
`(√7/2 - √3/4) s = (√(7/3) - 1/2) h`. -/
theorem candidate (s : ℝ) :
    (Real.sqrt 7 / 2 - Real.sqrt 3 / 4) * s
      = (Real.sqrt (7 / 3) - 1 / 2) * (Real.sqrt 3 / 2 * s) :=
