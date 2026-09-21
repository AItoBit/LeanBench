/--
If `b n` uses ordinary mathematical indexing, so that
`b 1 = a₁`, this is the same numerical conclusion.
-/
theorem candidate
    (b : ℕ → ℕ)

    (h1 :
      b 1 = 1)

    (hstep :
      ∀ n : ℕ,
        1 ≤ n →
        b n + 3 ≤
          b (n + 2)) :

    3034 ≤ b 2023 :=
