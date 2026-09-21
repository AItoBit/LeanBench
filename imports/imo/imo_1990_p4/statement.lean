/--
Exact minima for the two cycle models.
The reduction of the original problem to these models is not included.
-/
theorem candidate :
    (∀ n : ℕ, 1 ≤ n →
      IsLeast
        {k : ℕ | ForcesPairOddCycle (n - 1) k}
        n) ∧
    (∀ n q : ℕ, n = 3 * q + 2 →
      IsLeast
        {k : ℕ | ForcesPairThreeCycles q k}
        (n - 1)) :=
