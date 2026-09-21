namespace IMO2011P3

/-- The functional inequality from IMO 2011 Problem 3. -/
def Good (f : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ,
    f (x + y) ≤ y * f x + f (f x)
