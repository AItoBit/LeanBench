/-- **IMO 1972, Problem 4.**  The only positive solutions of the system are the
constant ones. -/
theorem candidate (x₁ x₂ x₃ x₄ x₅ : ℝ)
    (h₁ : 0 < x₁) (h₂ : 0 < x₂) (h₃ : 0 < x₃) (h₄ : 0 < x₄) (h₅ : 0 < x₅) :
    ((x₁ ^ 2 - x₃ * x₅) * (x₂ ^ 2 - x₃ * x₅) ≤ 0 ∧
     (x₂ ^ 2 - x₄ * x₁) * (x₃ ^ 2 - x₄ * x₁) ≤ 0 ∧
     (x₃ ^ 2 - x₅ * x₂) * (x₄ ^ 2 - x₅ * x₂) ≤ 0 ∧
     (x₄ ^ 2 - x₁ * x₃) * (x₅ ^ 2 - x₁ * x₃) ≤ 0 ∧
     (x₅ ^ 2 - x₂ * x₄) * (x₁ ^ 2 - x₂ * x₄) ≤ 0)
    ↔ (x₁ = x₂ ∧ x₁ = x₃ ∧ x₁ = x₄ ∧ x₁ = x₅) :=
