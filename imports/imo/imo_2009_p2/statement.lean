/--
A version that follows literally the chain displayed in the
published solution.
-/
theorem candidate
    (R OP OQ QB AQ AP PC MK ML : ℝ)
    (hOP : 0 ≤ OP)
    (hOQ : 0 ≤ OQ)
    (h1 :
      R ^ 2 - OQ ^ 2 = QB * AQ)
    (h2 :
      QB * AQ = 2 * AQ * MK)
    (h3 :
      2 * AQ * MK = 2 * AP * ML)
    (h4 :
      2 * AP * ML = AP * PC)
    (h5 :
      AP * PC = R ^ 2 - OP ^ 2) :
    OP = OQ :=
