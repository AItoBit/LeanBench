/-- Both pieces obtained by cutting the symmetric trapezoid with vertices
`(±a, 0)`, `(±b, h)` along the horizontal line at height `t` are again cyclic
quadrilaterals. -/
theorem candidate (a b h t : ℝ) (ht0 : 0 < t) (hth : t < h) :
    (∃ (o : ℂ) (r : ℝ),
      dist (pt a 0) o = r ∧ dist (pt (-a) 0) o = r ∧
      dist (pt (a + (b - a) * t / h) t) o = r ∧
      dist (pt (-(a + (b - a) * t / h)) t) o = r) ∧
    (∃ (o : ℂ) (r : ℝ),
      dist (pt (a + (b - a) * t / h) t) o = r ∧
      dist (pt (-(a + (b - a) * t / h)) t) o = r ∧
      dist (pt b h) o = r ∧ dist (pt (-b) h) o = r) :=
