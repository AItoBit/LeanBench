by

  constructor

  · intro lam hlam hlt

    have hlt' :
        lam < critical := by

      unfold critical

      exact hlt

    exact
      F.bazza
        lam
        hlam
        hlt'

  constructor

  · change
      NeitherWins critical

    exact
      F.equality

  · intro lam hgt

    have hgt' :
        critical < lam := by

      unfold critical

      exact hgt

    exact
      F.alice
        lam
        hgt'

/-!
============================================================
19. Classification as an iff for Alice
============================================================
-/
