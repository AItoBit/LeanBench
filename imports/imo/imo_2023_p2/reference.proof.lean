by

  have hperp :
      OnPerpBisector
        (fun X Y : EPoint => dist X Y)
        H A P := by

    exact
      euclidean_perp_bisector_of_PH_eq_AH
        hPH_AH

  have htan :
      ETangentAt ω P H := by

    exact
      perp_to_tangent
        hperp

  exact
    ⟨H,
     hBS,
     hbis,
     htan⟩
