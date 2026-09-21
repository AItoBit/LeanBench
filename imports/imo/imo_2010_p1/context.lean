namespace IMO2010P1

/-- The functional equation. -/
def Good (f : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ,
    f (((⌊x⌋ : ℤ) : ℝ) * y) =
      f x * (((⌊f y⌋ : ℤ) : ℝ))
