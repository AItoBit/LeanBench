namespace Imo2004P1

/-- Twice the signed area of a triangle. -/
def area2 (a1 a2 b1 b2 c1 c2 : ℝ) : ℝ := a1 * (b2 - c2) + b1 * (c2 - a2) + c1 * (a2 - b2)

/-- The concyclicity determinant of four points: it vanishes exactly when they are concyclic
or collinear. -/
def cyc (a1 a2 b1 b2 c1 c2 d1 d2 : ℝ) : ℝ :=
  (a1 ^ 2 + a2 ^ 2) * area2 b1 b2 c1 c2 d1 d2
  - (b1 ^ 2 + b2 ^ 2) * area2 a1 a2 c1 c2 d1 d2
  + (c1 ^ 2 + c2 ^ 2) * area2 a1 a2 b1 b2 d1 d2
  - (d1 ^ 2 + d2 ^ 2) * area2 a1 a2 b1 b2 c1 c2

/-- Converse power of a point: if `M` is on line `AB`, `R` is on line `AK`, and
`AM · AB = AR · AK`, then `B`, `M`, `R`, `K` are concyclic. -/
theorem cyc_of_pow_eq (a1 a2 b1 b2 k1 k2 m1 m2 r1 r2 s t : ℝ)
    (hm1 : m1 = a1 + s * (b1 - a1)) (hm2 : m2 = a2 + s * (b2 - a2))
    (hr1 : r1 = a1 + t * (k1 - a1)) (hr2 : r2 = a2 + t * (k2 - a2))
    (h : s * ((b1 - a1) ^ 2 + (b2 - a2) ^ 2) = t * ((k1 - a1) ^ 2 + (k2 - a2) ^ 2)) :
    cyc b1 b2 m1 m2 r1 r2 k1 k2 = 0 := by
  subst hm1 hm2 hr1 hr2
  simp only [cyc, area2]
  linear_combination
    (-(s - 1) * (t - 1) * (a1 * (b2 - k2) + b1 * (k2 - a2) + k1 * (a2 - b2))) * h
