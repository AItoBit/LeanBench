/-- **IMO 1985 P6.** -/
theorem candidate :
    ∃! a : ℝ, ∀ x : ℕ → ℝ, x 1 = a → (∀ n : ℕ, 1 ≤ n → x (n + 1) = x n * (x n + 1 / n)) →
      ∀ n : ℕ, 1 ≤ n → 0 < x n ∧ x n < x (n + 1) ∧ x (n + 1) < 1 :=
