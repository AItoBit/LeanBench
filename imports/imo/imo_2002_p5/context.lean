namespace IMO2002P5

/-- The functional equation in the problem. -/
def Satisfies (f : ℝ → ℝ) : Prop :=
  ∀ x y z t : ℝ,
    (f x + f z) * (f y + f t) = f (x * y - z * t) + f (x * t + y * z)
