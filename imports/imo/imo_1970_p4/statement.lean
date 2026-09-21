/-- **IMO 1970, Problem 4.** For no positive integer `n` can the set
`{n, n+1, n+2, n+3, n+4, n+5}` be split into two parts whose products agree. -/
theorem candidate (n : ℕ) (hn : 0 < n) :
    ¬ ∃ A : Finset ℕ, A ⊆ Finset.Icc n (n + 5) ∧
      ∏ x ∈ A, x = ∏ x ∈ Finset.Icc n (n + 5) \ A, x :=
