by

  have hpower :
      R ^ 2 - OQ ^ 2 =
        R ^ 2 - OP ^ 2 := by
    calc
      R ^ 2 - OQ ^ 2
          = QB * AQ := h1

      _ = 2 * AQ * MK := h2

      _ = 2 * AP * ML := h3

      _ = AP * PC := h4

      _ = R ^ 2 - OP ^ 2 := h5

  have hsquares :
      OP ^ 2 = OQ ^ 2 := by
    linarith

  nlinarith
