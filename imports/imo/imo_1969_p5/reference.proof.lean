by
  have h := imo1969_p5 S hcard hgen
  rwa [Nat.choose_two_right, show S.card - 3 - 1 = S.card - 4 from by omega] at h

/-! ### Sanity checks on the formalisation of "convex quadrilateral" -/
