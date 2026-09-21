namespace Imo2005P1

/-- Twice the signed area of a triangle; it vanishes exactly when the points are collinear. -/
def cross (a1 a2 b1 b2 c1 c2 : ℝ) : ℝ := (b1 - a1) * (c2 - a2) - (b2 - a2) * (c1 - a1)
