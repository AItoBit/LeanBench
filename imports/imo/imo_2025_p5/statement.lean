theorem candidate
    (F :
      StrategyFacts
        AliceWins
        BazzaWins
        NeitherWins) :
    (∀ lam : ℝ,
      0 < lam →
      lam < 1 / Real.sqrt 2 →
      BazzaWins lam)
    ∧
    NeitherWins (1 / Real.sqrt 2)
    ∧
    (∀ lam : ℝ,
      1 / Real.sqrt 2 < lam →
      AliceWins lam) :=
