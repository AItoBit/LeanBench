by

  have hconstruction :
      ∃ S : Square n,
        uphillCount S =
          target n := by

    obtain
      ⟨S, hS⟩ :=
      construction

    refine
      ⟨S, ?_⟩

    unfold target

    exact hS

  have hmain :
      IsMinimum
        Square
        uphillCount
        n
        (target n) :=
    imo2022_p6
      uphillCount
      n
      lower
      hconstruction

  unfold target at hmain

  exact hmain

/-!
============================================================
10. Explicit decomposition of the edge count
============================================================
-/
