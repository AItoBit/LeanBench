/--
Formalization of the algebraic core of the solution to IMO 1967 Problem 5.
-/
theorem candidate
    (a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ : ℝ)
    (h₁ : a₁ = -a₈)
    (h₂ : a₂ = -a₇)
    (h₃ : a₃ = -a₆)
    (h₄ : a₄ = -a₅)
    (k : ℕ) :
    (a₁^(2 * k + 1) + a₂^(2 * k + 1) + a₃^(2 * k + 1) + a₄^(2 * k + 1) +
     a₅^(2 * k + 1) + a₆^(2 * k + 1) + a₇^(2 * k + 1) + a₈^(2 * k + 1) = 0) ∧
    (0 ≤ a₁^(2 * k) + a₂^(2 * k) + a₃^(2 * k) + a₄^(2 * k) +
         a₅^(2 * k) + a₆^(2 * k) + a₇^(2 * k) + a₈^(2 * k)) :=
