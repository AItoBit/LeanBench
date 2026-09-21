/-- The three parts combined. -/
theorem candidate (A : ℝ) (S)
    (hS : S = {x : ℝ | 0 ≤ 2 * x - 1 ∧ 0 ≤ x + √(2 * x - 1) ∧
      0 ≤ x - √(2 * x - 1) ∧ √(x + √(2 * x - 1)) +
      √(x - √(2 * x - 1)) = A}) :
    (A = √2 → S = Set.Icc (1 / 2) 1) ∧ (A = 1 → S = ∅) ∧ (A = 2 → S = {3 / 2}) :=
