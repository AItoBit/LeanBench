by

  have hcover :
      n - k ≤ k * (k - 1) :=
    le_trans
      hblocked
      hred

  exact
    square_bound
      hkn
      hcover
