namespace IMO2012P4

/-- The original functional equation. -/
def Good (f : ℤ → ℤ) : Prop :=
  ∀ a b c : ℤ,
    a + b + c = 0 →
    f a ^ 2 + f b ^ 2 + f c ^ 2
      =
    2 * f a * f b +
    2 * f b * f c +
    2 * f c * f a

/-!
## f(0)=0
-/
