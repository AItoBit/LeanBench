by

  have harc :
      arcML = arcMK := by
    exact
      arc_ML_eq_arc_MK
        arcML arcMA arcKC arcMK
        angAKL angCPK angABL angKPS angPCS
        hML hMA hABL hAKL hPCS hMK

  calc
    MK
        = chord arcMK := hMKlen

    _ =
      chord arcML := by
        rw [harc]

    _ = ML := hMLlen.symm

/-!
## Alternative: Solution 2's final step

Solution 2 proves that `M` is the midpoint of arc `LK`.
Numerically, this means the two arcs from `M` to `K` and `M` to `L`
are equal.  The corresponding chords are therefore equal.
-/
