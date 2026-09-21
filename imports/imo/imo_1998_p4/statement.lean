theorem candidate (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (a * b ^ 2 + b + 7 ∣ a ^ 2 * b + a + b) ↔
      (a = 11 ∧ b = 1) ∨
      (a = 49 ∧ b = 1) ∨
      ∃ t : ℕ, 0 < t ∧ a = 7 * t ^ 2 ∧ b = 7 * t :=
