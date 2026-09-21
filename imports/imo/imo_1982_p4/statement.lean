/-- **IMO 1982, Problem 4 (b).**  No integer solutions for `n = 2891`. -/
theorem candidate : ¬ ∃ x y : ℤ, x ^ 3 - 3 * x * y ^ 2 + y ^ 3 = 2891 :=
