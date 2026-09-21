by

  have hA :
      EquidistantCenter A F G :=
    equal_radii_A
      hAFAG

  have hO :
      EquidistantCenter O F G :=
    equal_radii_O
      hOFOG

  exact
    imo2015_p4_final
      A
      O
      F
      G
      X
      hFG
      hA
      hO
      hXFXG
