/-- **IMO 1972, Problem 5.** -/
theorem candidate (f g : ℝ → ℝ)
    (hfg : ∀ x y, f (x + y) + f (x - y) = 2 * f x * g y)
    (hf1 : ∀ x, |f x| ≤ 1)
    (hnz : ∃ x, f x ≠ 0) :
    ∀ y, |g y| ≤ 1 :=
