/-- **IMO 1977, Problem 4.** -/
theorem candidate (a b A B : ℝ)
    (h : ∀ x : ℝ,
      0 ≤ 1 - a * Real.cos x - b * Real.sin x
            - A * Real.cos (2 * x) - B * Real.sin (2 * x)) :
    a ^ 2 + b ^ 2 ≤ 2 ∧ A ^ 2 + B ^ 2 ≤ 1 :=
