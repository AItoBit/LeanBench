pointB
    let C := pointC
    let M := pointM a c
    let N := pointN a b
    let D := pointD a b c

    Collinear B M D ∧
    Collinear C N D ∧
    OnCircumcircle a b c D := by

  dsimp

  exact
    imo2014_p4_barycentric_core
      a b c
