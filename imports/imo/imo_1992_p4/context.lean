namespace Imo1992P4

/-- `P = (x,y)` lies on the tangent to `x² + y² = r²` drawn from `(t,-r)` other than `y = -r`. -/
def OnTangent (r t x y : ℝ) : Prop := 2 * r * t * x + (t ^ 2 - r ^ 2) * y = r * (t ^ 2 + r ^ 2)
