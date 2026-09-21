/--
There exists a strictly increasing `f : ℕ → ℕ` such that `f 1 = 2` and
`f (f n) = f n + n`.  This is slightly stronger than the problem, whose
natural numbers start at `1`, because the identity is also proved at `0`.
-/
theorem candidate :
    ∃ f : ℕ → ℕ, StrictMono f ∧ f 1 = 2 ∧ ∀ n, f (f n) = f n + n :=
