theorem candidate
    (x₁ x₂ x₃ x₄ x₅ : ℤ) :
    f x₁ x₂ (x₃ + x₄) (-x₄) (x₅ + x₄) - f x₁ x₂ x₃ x₄ x₅ =
    2 * (x₁ + x₂ + x₃ + x₄ + x₅) * x₄ :=
