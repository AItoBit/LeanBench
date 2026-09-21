/-- IMO 1969 Problem 6 is sharp: equality holds when `x₁ = x₂`, `y₁ = y₂`, `z₁ = z₂`. -/
theorem candidate (x y z : ℝ) (hA : 0 < x * y - z ^ 2) :
    8 / ((x + x) * (y + y) - (z + z) ^ 2)
      = 1 / (x * y - z ^ 2) + 1 / (x * y - z ^ 2) :=
