/-- The incenter of a triangle in barycentric form: with `a`, `b`, `c` the lengths of the sides
opposite to the vertices `p₀`, `p₁`, `p₂`, we have
`(a + b + c) • incenter = a • p₀ + b • p₁ + c • p₂`. -/
theorem candidate (t : Triangle ℝ V) :
    (dist (t.points 1) (t.points 2) + dist (t.points 0) (t.points 2) +
        dist (t.points 0) (t.points 1)) • t.incenter =
      dist (t.points 1) (t.points 2) • t.points 0 + dist (t.points 0) (t.points 2) • t.points 1 +
        dist (t.points 0) (t.points 1) • t.points 2 :=
