/-- **IMO 1999, Problem 3.**  For an even positive integer `n`, the least number of cells of an
`n × n` board that can be marked so that every cell of the board has a marked neighbour is
`n * (n + 2) / 4`. -/
theorem candidate {n : ℕ} (hpos : 0 < n) (hn : Even n) :
    IsLeast {k | ∃ S : Finset (ℕ × ℕ), S ⊆ board n ∧ S.card = k ∧ Good n S} (n * (n + 2) / 4) :=
