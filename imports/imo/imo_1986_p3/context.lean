namespace IMO1986P3

/-- The semi-invariant function f for the 5-tuple. -/
def f (v₁ v₂ v₃ v₄ v₅ : ℤ) : ℤ :=
  (v₁ - v₃)^2 + (v₂ - v₄)^2 + (v₃ - v₅)^2 + (v₄ - v₁)^2 + (v₅ - v₂)^2
