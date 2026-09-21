/-- Key algebraic simplification: if `0 ≤ 1 + 2 * x` and `(1 - √(1 + 2 * x)) ^ 2 ≠ 0`, then
`4 * x ^ 2 / (1 - √(1 + 2 * x)) ^ 2 = (1 + √(1 + 2 * x)) ^ 2`. -/
theorem imo_1960_p2_div_eq (x : ℝ) (hx : 0 ≤ 1 + 2 * x) (hne : (1 - √(1 + 2 * x)) ^ 2 ≠ 0) :
    4 * x ^ 2 / (1 - √(1 + 2 * x)) ^ 2 = (1 + √(1 + 2 * x)) ^ 2 := by
  have ht : √(1 + 2 * x) ^ 2 = 1 + 2 * x := Real.sq_sqrt hx
  rw [div_eq_iff hne]
  nlinarith [ht]
