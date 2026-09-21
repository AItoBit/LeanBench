/-- **IMO 1988, Problem 1 (ii), exact locus.**  The same circle, minus the same two points,
is described by the midpoint `V` of `AC`. -/
theorem candidate {R r : ℝ} (hr : 0 < r) (hrR : r < R) {O P : Pt}
    (hP : dist P O = r) :
    {X : Pt | ∃ A B C : Pt, Config R r O A P B C ∧ X = midpoint ℝ A C}
      = Metric.sphere (midpoint ℝ O P) (R / 2)
        \ {midpoint ℝ O P + (1 * R / (2 * r)) • (P - O),
           midpoint ℝ O P + (-1 * R / (2 * r)) • (P - O)} :=
