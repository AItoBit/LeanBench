theorem candidate (f : ℕ → ℕ) :
    (∀ m n, f (m + f n) = f (f m) + f n) ↔
      (∀ n, f n = 0) ∨
        ∃ d : ℕ, 0 < d ∧ ∃ a : ℕ → ℕ, a 0 = 0 ∧ ∀ n, f n = d * (a (n % d) + n / d) :=
