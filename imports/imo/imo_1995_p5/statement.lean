/-- **IMO 1995, Problem 5.**  Let `ABCDEF` be a convex hexagon with `AB = BC = CD` and
`DE = EF = FA`, such that `∠BCD = ∠EFA = π/3`.  If `G` and `H` are points in the interior
of the hexagon with `∠AGB = ∠DHE = 2π/3`, then `AG + GB + GH + DH + HE ≥ CF`.

The hypotheses `hG`, `hH`, `hGmem`, `hHmem` concerning the two points `G` and `H` are part
of the original statement and are kept here, but the inequality in fact holds for arbitrary
points `G` and `H`, so they are not used in the proof. -/
theorem candidate (A B C D E F G H : ℂ)
    (hconv : ConvexHexagon A B C D E F)
    (hAB : dist A B = dist B C) (hBC : dist B C = dist C D)
    (hDE : dist D E = dist E F) (hEF : dist E F = dist F A)
    (hangC : EuclideanGeometry.angle B C D = π / 3)
    (hangF : EuclideanGeometry.angle E F A = π / 3)
    (hG : EuclideanGeometry.angle A G B = 2 * π / 3)
    (hH : EuclideanGeometry.angle D H E = 2 * π / 3)
    (hGmem : G ∈ interior (convexHull ℝ ({A, B, C, D, E, F} : Set ℂ)))
    (hHmem : H ∈ interior (convexHull ℝ ({A, B, C, D, E, F} : Set ℂ))) :
    dist C F ≤ dist A G + dist G B + dist G H + dist D H + dist H E :=
