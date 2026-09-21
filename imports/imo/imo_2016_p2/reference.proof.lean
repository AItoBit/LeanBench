by

  have hcount' :
      k * k = 3 * a :=
    hcount.symm

  exact
    nine_dvd_of_reduced_count
      hn
      hcount'

/-!
## Converse at the arithmetic level
-/
