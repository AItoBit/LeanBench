/-- **IMO 2003 P2.** -/
theorem candidate (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    (∃ k : ℤ, 0 < k ∧ a ^ 2 = k * (2 * a * b ^ 2 - b ^ 3 + 1)) ↔
      (∃ n : ℤ, 0 < n ∧ ((a = 2 * n ∧ b = 1) ∨ (a = n ∧ b = 2 * n) ∨
        (a = 8 * n ^ 4 - n ∧ b = 2 * n))) :=
