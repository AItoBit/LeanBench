/--
For which real values of `p` does the equation `√(x²-p) + 2√(x²-1) = x` have real roots?
Answer: exactly when `0 ≤ p ≤ 4/3`, and then the unique root is `(4-p)/(2√(4-2p))`.
-/
theorem candidate (p : ℝ) :
    {x : ℝ | 0 ≤ x ^ 2 - p ∧ 0 ≤ x ^ 2 - 1 ∧ √(x ^ 2 - p) + 2 * √(x ^ 2 - 1) = x}
      = if 0 ≤ p ∧ p ≤ 4 / 3 then {(4 - p) / (2 * √(4 - 2 * p))} else ∅ :=
