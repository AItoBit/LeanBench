/-- **IMO 1979, Problem 3.** There is a fixed point `P` in the plane from which the two moving
points are always equidistant. -/
theorem candidate (O₁ O₂ A : ℂ) (h : O₁ ≠ O₂) :
    ∃ P : ℂ, ∀ t : ℝ,
      dist (imo1979P3Motion O₁ A t) P = dist (imo1979P3Motion O₂ A t) P :=
