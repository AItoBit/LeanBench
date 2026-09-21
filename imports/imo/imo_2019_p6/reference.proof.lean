by

  have hQ :
      OnCircle Ω Q := by

    exact
      step4
        ang
        OnCircle
        hP
        hS
        hM
        hPQM_PQC
        hPQC_PEC
        hPEC_PED
        hPED_PSD
        hPSD_PSM
        q_membership

  exact
    final_reduction
      OnCircle
      Collinear
      Perpendicular
      hQ
      reduction
