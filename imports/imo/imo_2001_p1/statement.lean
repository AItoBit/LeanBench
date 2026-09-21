/-- IMO 2001, Problem 1, with the altitude foot and circumcenter constructed by mathlib. -/
theorem candidate (t : Affine.Triangle ℝ E)
    (hA : ∠ (t.points 1) (t.points 0) (t.points 2) < π / 2)
    (hB : ∠ (t.points 0) (t.points 1) (t.points 2) < π / 2)
    (hC : ∠ (t.points 0) (t.points 2) (t.points 1) < π / 2)
    (hgap : ∠ (t.points 0) (t.points 1) (t.points 2) + π / 6 ≤
      ∠ (t.points 0) (t.points 2) (t.points 1)) :
    ∠ (t.points 1) (t.points 0) (t.points 2) +
      ∠ (t.points 2) t.circumcenter (altitudeFoot t) < π / 2 :=
