/-- The two facts combined: every developed path from `x` to `x'`, where `x` and
`x'` are at distance `r` from `c`, has length at least `2 * r * sin (α / 2)`
with `α = ∠ x c x'`.  This is the lower bound of part (b). -/
theorem candidate {x y z t x' c : P} {r : ℝ}
    (hx : dist x c = r) (hx' : dist x' c = r) :
    2 * r * Real.sin (∠ x c x' / 2) ≤ dist x y + dist y z + dist z t + dist t x' :=
