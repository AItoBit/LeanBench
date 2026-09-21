by

  intro a b ha hb

  constructor

  · intro h

    obtain
      ⟨D,
       g,
       hgpos,
       hgform,
       hEuler⟩ :=
      source_reduction
        ha
        hb
        h

    exact
      endgame
        D
        hgpos
        hgform
        hEuler

  · intro h

    rcases h with
      ⟨rfl, rfl⟩

    exact
      one_one_works
