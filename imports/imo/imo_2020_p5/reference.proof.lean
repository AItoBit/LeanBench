by

  have hnot :
      ¬ (¬ AllEqual s) := by

    exact
      imo2020_p5_descent
        μ
        PositiveState
        GoodState
        (fun x => ¬ AllEqual x)
        hstep
        s
        hpos
        hgood

  by_contra hne

  exact
    hnot hne
