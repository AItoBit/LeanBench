by

  rcases hgood with
    ⟨ha, _hb, hc, _h₁, _h₂, _h₃⟩

  constructor

  · exact
      first_le_second
        ha
        hbc

  · exact
      second_le_third
        hc
        hab
