namespace Imo1973P3

/-- **IMO 1973, Problem 3.** -/

theorem candidate :
    IsLeast {y : ℝ | ∃ a b : ℝ,
      (∃ x : ℝ, x ^ 4 + a * x ^ 3 + b * x ^ 2 + a * x + 1 = 0) ∧ y = a ^ 2 + b ^ 2}
      (4 / 5) :=
