/-- The line `OnTangent r t` is at distance `r` from the origin, so it is tangent to `C`.
Written in cleared form: for `A x + B y = C`, the condition is `C² = r²(A² + B²)`. -/
theorem tangent_is_tangent (r t : ℝ) :
    (r * (t ^ 2 + r ^ 2)) ^ 2 = r ^ 2 * ((2 * r * t) ^ 2 + (t ^ 2 - r ^ 2) ^ 2) := by
  ring

/-- The line `OnTangent r t` passes through `(t, -r)`. -/
theorem tangent_through (r t : ℝ) : OnTangent r t t (-r) := by
  unfold OnTangent; ring
