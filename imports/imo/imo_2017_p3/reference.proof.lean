by

  have hgrowth :=
    iterated_half_growth D h 20000

  rcases hgrowth with hgrowth | hzero

  · norm_num at hgrowth ⊢
    exact hgrowth

  · norm_num at hzero
