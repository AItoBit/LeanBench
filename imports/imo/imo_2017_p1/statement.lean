/--
If `3 ∣ a₀` and a term of the sequence reaches one
of `3,6,9`, then the source's required infinite repetition
property follows.
-/
theorem candidate
    {a : ℕ → ℕ}
    (hrec :
      FollowsRecurrence a)
    (h0 :
      3 ∣ a 0)
    {n₀ : ℕ}
    (hcycle :
      a n₀ = 3 ∨
      a n₀ = 6 ∨
      a n₀ = 9) :
    (∀ n : ℕ, 3 ∣ a n) ∧
    (∀ N : ℕ,
      ∃ n : ℕ,
        N ≤ n ∧
        a n = 3) :=
