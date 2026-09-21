by

  refine
    ⟨v + 1,
     N + 1,
     ?_,
     ?_,
     ?_⟩

  · linarith

  · omega

  · intro m n hm hmn

    have hmN :
        N ≤ m := by
      omega

    exact
      eventual_pattern_bound
        a
        w
        v
        N
        hv0
        hv2014
        hrec
        hweight
        m
        n
        hmN
        hmn

/-!
## Explicit T = 2014 identity
-/
