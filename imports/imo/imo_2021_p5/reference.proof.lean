by

  obtain
    ⟨j,
     hj,
     hbetween⟩ :=
    imo2021_p5_parity_core
      left
      right
      badCount
      hstart
      hfinal
      hpreserve

  obtain
    ⟨a,
     b,
     habPair,
     hak,
     hkb⟩ :=
    between_gives_ordered_pair
      hbetween

  have hbounds :
      1 ≤ j + 1 ∧
      j + 1 ≤ 2021 :=
    move_number_bounds
      hj

  have hpred :
      (j + 1) - 1 = j := by
    omega

  refine
    ⟨j + 1,
     a,
     b,
     hbounds.1,
     hbounds.2,
     hak,
     hkb,
     ?_⟩

  rw [hpred]

  exact habPair
