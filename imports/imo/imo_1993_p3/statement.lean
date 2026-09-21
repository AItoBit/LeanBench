/-- **IMO 1993 P3, impossibility half.** If `3 ∣ n` the game on the `n × n` board can never be
reduced to a single piece. -/
theorem candidate (m : ℕ) (S : Finset Pos)
    (h : Relation.ReflTransGen Move (board (3 * m)) S) : S.card ≠ 1 :=
