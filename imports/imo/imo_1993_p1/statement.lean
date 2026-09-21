/-- **IMO 1993 P1.** -/
theorem candidate (n : ℕ) (hn : 1 < n) :
    ¬ ∃ g h : ℤ[X], 0 < g.natDegree ∧ 0 < h.natDegree ∧
      g * h = X ^ n + C 5 * X ^ (n - 1) + C 3 :=
