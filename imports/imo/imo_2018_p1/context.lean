namespace Imo2018P1

/-- The Euclidean plane. -/
abbrev Pt := ℝ × ℝ

/-- The standard inner product. -/
def dotp (x y : Pt) : ℝ := x.1 * y.1 + x.2 * y.2

/-- The scalar cross product. `crossp x y = 0` exactly when `x` and `y` are parallel. -/
def crossp (x y : Pt) : ℝ := x.1 * y.2 - x.2 * y.1
