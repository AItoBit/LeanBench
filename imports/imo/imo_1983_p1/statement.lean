/-- The function `x ↦ 1/x` does satisfy the two conditions. -/
theorem candidate :
    (∀ x : ℝ, 0 < x → 0 < 1 / x) ∧
    (∀ x y : ℝ, 0 < x → 0 < y → 1 / (x * (1 / y)) = y * (1 / x)) ∧
    Filter.Tendsto (fun x : ℝ => 1 / x) Filter.atTop (nhds 0) :=
