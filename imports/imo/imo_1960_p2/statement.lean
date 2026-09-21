/-- For what real values of `x` does `4x²/(1-√(1+2x))² < 2x + 9` hold?
The answer is `-1/2 ≤ x < 45/8`, except `x = 0`. -/
theorem candidate :
    {x : ℝ | 0 ≤ 1 + 2 * x ∧ (1 - √(1 + 2 * x)) ^ 2 ≠ 0 ∧
      4 * x ^ 2 / (1 - √(1 + 2 * x)) ^ 2 < 2 * x + 9} =
    Set.Ico (-(1 / 2)) (45 / 8) \ {0} :=
