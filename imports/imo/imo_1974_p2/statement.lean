/-- **IMO 1974, Problem 2.**  In a (nondegenerate) triangle `ABC` there is a point `D` on the
side `AB` such that `CD` is the geometric mean of `AD` and `DB` if and only if
`sin A * sin B ≤ sin (C / 2) ^ 2`. -/
theorem candidate {A B C : Plane} (h : ¬ Collinear ℝ ({A, B, C} : Set Plane)) :
    (∃ D ∈ segment ℝ A B, dist C D ^ 2 = dist A D * dist D B) ↔
      Real.sin (∠ B A C) * Real.sin (∠ A B C) ≤ Real.sin (∠ A C B / 2) ^ 2 :=
