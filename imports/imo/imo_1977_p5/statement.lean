/-- **IMO 1977, Problem 5.** -/
theorem candidate (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (∃ q r : ℕ, a ^ 2 + b ^ 2 = q * (a + b) + r ∧ r < a + b ∧ q ^ 2 + r = 1977)
      ↔ ((a = 50 ∧ b = 37) ∨ (a = 37 ∧ b = 50) ∨
          (a = 50 ∧ b = 7) ∨ (a = 7 ∧ b = 50)) :=
