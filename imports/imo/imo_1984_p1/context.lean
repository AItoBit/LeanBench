namespace IMO1984A1

variable (x y z : ℝ)

/-- The target symmetric expression. -/
def target : ℝ := y * z + z * x + x * y - 2 * x * y * z
