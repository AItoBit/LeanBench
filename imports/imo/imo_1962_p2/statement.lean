/-- **IMO 1962, Problem 2.**  The set of real `x` with `3 - x ≥ 0`, `x + 1 ≥ 0` and
`√(3 - x) - √(x + 1) > 1/2` is exactly `[-1, 1 - √31/8)`. -/
theorem candidate :
    {x : ℝ | 0 ≤ 3 - x ∧ 0 ≤ x + 1 ∧ 1 / 2 < √(3 - x) - √(x + 1)} =
      Set.Ico (-1) (1 - √31 / 8) :=
