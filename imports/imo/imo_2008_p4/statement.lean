/-- **IMO 2008, Problem 4.** For `f` positive on the positive reals, `f` satisfies the
functional equation if and only if `f x = x` for all `x > 0` or `f x = 1 / x` for all
`x > 0`. -/
theorem candidate (f : ℝ → ℝ) (hpos : ∀ x : ℝ, 0 < x → 0 < f x) :
    FE f ↔ ((∀ x : ℝ, 0 < x → f x = x) ∨ (∀ x : ℝ, 0 < x → f x = 1 / x)) :=
