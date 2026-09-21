/-- Both conclusions of IMO 2007 Problem 1. -/
theorem candidate (a : Fin (n + 1) → ℝ) :
    (∀ x : Fin (n + 1) → ℝ, Monotone x → d a / 2 ≤ error a x) ∧
    (∃ x : Fin (n + 1) → ℝ, Monotone x ∧ error a x = d a / 2) :=
