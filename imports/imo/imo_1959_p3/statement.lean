/-- Comparison for `a = 4`, `b = 2`, `c = -1`: after dividing by the common factor `4`, the
equation in `cos (2 * x)` is `4 * y ^ 2 + 2 * y - 1 = 0`, i.e. exactly the same quadratic as the
original one in `cos x`. -/
theorem candidate (y : ℝ) :
    imo1959P3F₀ 4 2 (-1) * y ^ 2 + imo1959P3F₁ 4 2 (-1) * y + imo1959P3F₂ 4 2 (-1)
      = 4 * (4 * y ^ 2 + 2 * y - 1) :=
