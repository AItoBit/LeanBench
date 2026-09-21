by

  obtain
    ⟨Gfinal,
     hreach,
     hgood⟩ :=
    imo2019_p3_algorithm
      edgeCount
      Event
      Connected
      Acyclic
      Good
      hdecrease
      hcycleStep
      hforestStep
      G₀
      hConnected

  exact
    ⟨Gfinal,
     hreach,
     hGood Gfinal hgood⟩
