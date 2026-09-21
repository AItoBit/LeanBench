open Real

/-- Formalization of the system derivation.
Assume `a₁ > a₂ > a₃ > a₄` (so all absolute values become signed differences)
and that the three linear relations obtained by pairwise subtraction hold:
  -x₁ + x₂ + x₃ + x₄ = 0
  -x₁ - x₂ - x₃ + x₄ = 0
  -x₁ - x₂ + x₃ + x₄ = 0
Then `x₂ = x₃ = 0`, hence `x₁ = x₄`, and substituting back gives
`x₁ = x₄ = 1/(a₁-a₄)`. -/

theorem candidate
    (a1 a2 a3 a4 x1 x2 x3 x4 : ℝ)
    (ha : a1 > a2 ∧ a2 > a3 ∧ a3 > a4)
    (h0 : (a1 - a2) * x2 + (a1 - a3) * x3 + (a1 - a4) * x4 = 1)
    (h1 : -x1 + x2 + x3 + x4 = 0)
    (h2 : -x1 - x2 - x3 + x4 = 0)
    (h3 : -x1 - x2 + x3 + x4 = 0)
    (_hneq : a1 ≠ a4) :
    x2 = 0 ∧ x3 = 0 ∧ x1 = x4 ∧ x1 = 1 / (a1 - a4) :=
