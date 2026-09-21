theorem candidate
    (a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ x₁ x₂ x₃ : ℝ)
    -- (a) diagonal entries are positive
    (hp₁ : 0 < a₁₁) (hp₂ : 0 < a₂₂) (hp₃ : 0 < a₃₃)
    -- (b) off-diagonal entries are negative
    (hn₁₂ : a₁₂ < 0) (hn₁₃ : a₁₃ < 0)
    (hn₂₁ : a₂₁ < 0) (hn₂₃ : a₂₃ < 0)
    (hn₃₁ : a₃₁ < 0) (hn₃₂ : a₃₂ < 0)
    -- (c) each row sum is positive
    (hs₁ : 0 < a₁₁ + a₁₂ + a₁₃)
    (hs₂ : 0 < a₂₁ + a₂₂ + a₂₃)
    (hs₃ : 0 < a₃₁ + a₃₂ + a₃₃)
    (e₁ : a₁₁ * x₁ + a₁₂ * x₂ + a₁₃ * x₃ = 0)
    (e₂ : a₂₁ * x₁ + a₂₂ * x₂ + a₂₃ * x₃ = 0)
    (e₃ : a₃₁ * x₁ + a₃₂ * x₂ + a₃₃ * x₃ = 0) :
    x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 :=
