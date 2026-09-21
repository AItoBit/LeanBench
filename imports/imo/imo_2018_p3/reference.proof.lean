by

  have hnonlarge :
      nonlarge ≤ 126 :=
    bottom_nonlarge_upper_bound
      hentries
      hlarge

  have hbad252 :
      bad ≤ 252 := by

    calc
      bad
          ≤ 2 * nonlarge :=
        hbad

      _ ≤ 2 * 126 := by
        omega

      _ = 252 := by
        norm_num

  have hgood :
      1765 ≤ goodPairs.card := by

    exact
      many_large_adjacent_pairs
        hpairs
        hbad252

  exact
    final_counting_contradiction
      goodPairs
      exception
      hgood
      hforbidden

/-!
## Combined numerical summary
-/
