by

  constructor

  · exact
      every_play_is_finite
        F
        initial

  constructor

  · intro final hreach hstop

    exact
      terminal_shape
        F
        hinit
        hreach
        hstop

  · intro final₁ final₂ M₁ M₂ hreach₁ hreach₂ hfinal₁ hfinal₂

    exact
      final_value_unique
        F
        hreach₁
        hreach₂
        hfinal₁
        hfinal₂
