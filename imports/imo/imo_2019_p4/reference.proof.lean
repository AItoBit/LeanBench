by

  constructor

  · intro h

    exact
      classify_bounded
        hk
        hn
        (hbound
          k
          n
          hk
          hn
          h)
        h

  · intro h

    rcases h with h | h

    · rcases h with
        ⟨rfl, rfl⟩

      norm_num [rhs]

    · rcases h with
        ⟨rfl, rfl⟩

      norm_num [rhs]
