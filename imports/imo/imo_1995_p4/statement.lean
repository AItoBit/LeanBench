/-- **IMO 1995, Problem 4.** The maximum value that `x 0` can have is `2 ^ 997`. -/
theorem candidate :
    IsGreatest {a : ℝ | ∃ x : ℕ → ℝ, Constraint x ∧ x 0 = a} ((2 : ℝ) ^ (997 : ℕ)) :=
