/-- **IMO 2005, Problem 3.** For positive reals `x, y, z` with `xyz ≥ 1`,
`(x⁵ - x²)/(x⁵ + y² + z²) + (y⁵ - y²)/(x² + y⁵ + z²) + (z⁵ - z²)/(x² + y² + z⁵) ≥ 0`. -/
theorem candidate (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : 1 ≤ x * y * z) :
    0 ≤ (x ^ 5 - x ^ 2) / (x ^ 5 + y ^ 2 + z ^ 2)
      + (y ^ 5 - y ^ 2) / (x ^ 2 + y ^ 5 + z ^ 2)
      + (z ^ 5 - z ^ 2) / (x ^ 2 + y ^ 2 + z ^ 5) :=
