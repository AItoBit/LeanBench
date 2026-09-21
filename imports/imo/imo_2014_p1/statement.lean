theorem candidate
    (a : ℕ → ℕ)
    (hpos :
      ∀ n : ℕ,
        0 < a n)
    (hinc :
      ∀ n : ℕ,
        a n < a (n + 1)) :
    ∃! n : ℕ,
      GoodIndex a n :=
