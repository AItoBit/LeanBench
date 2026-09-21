namespace Imo1989P2

variable {a b c r S : ℝ}

/-- Area of the hexagon `AC₁BA₁CB₁`: the triangle plus the three circular "ears". -/
noncomputable def hexArea (a b c r S : ℝ) : ℝ :=
  S + (1 / 4) * a ^ 2 * (2 * r / (b + c - a))
    + (1 / 4) * b ^ 2 * (2 * r / (c + a - b))
    + (1 / 4) * c ^ 2 * (2 * r / (a + b - c))

/-- Area of the excentral triangle `A₀B₀C₀`: the triangle plus the three triangles
`A₀BC`, `B₀CA`, `C₀AB`, each of area `½ · side · exradius`. -/
noncomputable def excentralArea (a b c r S : ℝ) : ℝ :=
  S + (1 / 2) * a * (r * (a + b + c) / (b + c - a))
    + (1 / 2) * b * (r * (a + b + c) / (c + a - b))
    + (1 / 2) * c * (r * (a + b + c) / (a + b - c))
