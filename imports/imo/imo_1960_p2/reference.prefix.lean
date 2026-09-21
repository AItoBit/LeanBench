open scoped Real

open scoped Nat

/-!
# IMO 1960 Problem 2

For what real values of `x` does the inequality
`4 * x ^ 2 / (1 - √(1 + 2 * x)) ^ 2 < 2 * x + 9` hold?

Answer: exactly for `-1/2 ≤ x < 45/8` with `x ≠ 0`.

The original submission was stated with the competition-problem markers
`@[imo_problem_subject algebra]` and `answer(...)`, which are not available in
this project; the statement below is the same set equality with those wrappers
removed.
-/

/-- Key algebraic simplification: if `0 ≤ 1 + 2 * x` and `(1 - √(1 + 2 * x)) ^ 2 ≠ 0`, then
`4 * x ^ 2 / (1 - √(1 + 2 * x)) ^ 2 = (1 + √(1 + 2 * x)) ^ 2`. -/
theorem imo_1960_p2_div_eq (x : ℝ) (hx : 0 ≤ 1 + 2 * x) (hne : (1 - √(1 + 2 * x)) ^ 2 ≠ 0) :
    4 * x ^ 2 / (1 - √(1 + 2 * x)) ^ 2 = (1 + √(1 + 2 * x)) ^ 2 := by
  have ht : √(1 + 2 * x) ^ 2 = 1 + 2 * x := Real.sq_sqrt hx
  rw [div_eq_iff hne]
  nlinarith [ht]
