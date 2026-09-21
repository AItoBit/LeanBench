by

  have hAB :
      dist O A =
        dist O B :=
    equal_dist_to_A_B
      dist
      hOA
      hOB

  have hPB :
      OnPerpBisector O A B :=
    perpCriterion hAB

  exact
    ⟨O,
     hD,
     hC,
     hPB⟩
