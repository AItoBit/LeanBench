/--
Point-valued final conclusion: `M` itself equals the midpoint of `ST`.
-/
theorem candidate
    (s m t j : ℝ)
    (hst : s ≠ t)
    (hJ :
      sqDist (m, j) (s, 0) =
        sqDist (m, j) (t, 0)) :
    ((m, 0) : Point) =
      midpoint (s, 0) (t, 0) :=
