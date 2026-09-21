/-- **IMO 1974, Problem 4**, second part: for the maximal value `p = 7`, the set of sequences
`a 1 < a 2 < ⋯ < a 7` arising from such a decomposition is exactly the set of the four sequences
`1,2,3,4,5,7,10`, `1,2,3,4,5,8,9`, `1,2,3,4,6,7,9`, `1,2,3,5,6,7,8`. -/
theorem candidate :
    {L : List ℕ | ∃ R : Fin 7 → Rect, IsGood R ∧ List.ofFn (fun i => whiteCount (R i)) = L} =
      {L : List ℕ | L ∈ answerSeqs} :=
