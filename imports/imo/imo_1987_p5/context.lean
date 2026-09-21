namespace Imo1987P5

/-- Euclidean distance between two points of `ℝ × ℝ`.
(Mathlib's `dist` on `ℝ × ℝ` is the sup metric, so we write it out.) -/
noncomputable def eDist (p q : ℝ × ℝ) : ℝ :=
  Real.sqrt ((p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2)

/-- Area of the triangle `pqr` (shoelace formula). It is `0` iff the points are collinear. -/
noncomputable def triArea (p q r : ℝ × ℝ) : ℝ :=
  |(q.1 - p.1) * (r.2 - p.2) - (r.1 - p.1) * (q.2 - p.2)| / 2
