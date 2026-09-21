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
