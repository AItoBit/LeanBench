theorem candidate (n : ℕ) (hn : 2 ≤ n)
    (h : ∀ k : ℕ, (k : ℝ) ≤ Real.sqrt (n / 3) → Nat.Prime (k ^ 2 + k + n)) :
    ∀ k : ℕ, k ≤ n - 2 → Nat.Prime (k ^ 2 + k + n) :=
