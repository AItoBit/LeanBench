/-- **IMO 1977, Problem 3.** -/
theorem candidate (n : ℕ) (hn : 2 < n) :
    ∃ r A B C D : ℕ, V n r ∧
      Indec n A ∧ Indec n B ∧ Indec n C ∧ Indec n D ∧
      r = A * B ∧ r = C * D ∧ A ≠ C ∧ A ≠ D :=
