/-- **IMO 1973, Problem 1.** -/
theorem candidate (n : ℕ) (hodd : Odd n) (v : Fin n → ℂ)
    (hunit : ∀ i, ‖v i‖ = 1) (hside : ∀ i, 0 ≤ (v i).im) :
    1 ≤ ‖∑ i, v i‖ :=
