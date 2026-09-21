/-- The originally proposed version of the statement, which omits the condition `0 < a`,
is false: for `a = -2`, `b = Real.sqrt 2` the right-hand side holds while there are of course
no positive `x, y, z` summing to a negative number. -/
theorem candidate :
    ¬ ∀ a b : ℝ,
      (∃ x > (0 : ℝ), ∃ y > (0 : ℝ), ∃ z > (0 : ℝ),
        x + y + z = a ∧
        x ^ 2 + y ^ 2 + z ^ 2 = b ^ 2 ∧
        x * y = z ^ 2 ∧
        [x, y, z].Nodup) ↔
      (b ^ 2 < a ^ 2 ∧ a ^ 2 < 3 * b ^ 2) :=
