by

  intro n hn pile

  obtain ⟨T, _⟩ :=
    exists_good_triple
      n
      hn

  exact
    pair_in_same_pile
      T
      pile

/-!
============================================================
6. Explicit square identities from the source
============================================================
-/
