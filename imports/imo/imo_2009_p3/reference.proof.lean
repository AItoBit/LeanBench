by

  have hmm :
      m = M := by
    exact
      min_eq_max
        s gap
        m M imin imax
        hmpos hMpos
        hlower hupper
        hminBlock hmaxBlock
        himageConstant

  have hconst :
      ∀ n : ℕ,
        gap n = m := by
    exact
      constant_gap_of_min_eq_max
        gap m M
        hlower hupper hmm

  exact
    isArithmetic_of_constant_gap
      s gap hgap m hconst
