/-- **IMO 2006 P3.** -/
theorem candidate :
    IsLeast {M : ℝ | ∀ a b c : ℝ,
        |a * b * (a ^ 2 - b ^ 2) + b * c * (b ^ 2 - c ^ 2) + c * a * (c ^ 2 - a ^ 2)|
          ≤ M * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2}
      (9 * Real.sqrt 2 / 32) :=
