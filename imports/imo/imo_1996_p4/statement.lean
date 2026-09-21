theorem candidate :
    IsLeast {k : ℕ | ∃ a b m n : ℕ, 0 < a ∧ 0 < b ∧ 0 < m ∧ 0 < n ∧
      15 * a + 16 * b = m ^ 2 ∧ 16 * a = 15 * b + n ^ 2 ∧ k = min (m ^ 2) (n ^ 2)}
      231361 :=
