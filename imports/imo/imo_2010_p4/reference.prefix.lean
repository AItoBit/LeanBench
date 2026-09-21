namespace IMO2010P4

/-!
## Algebraic angle-chasing core
-/

/--
The numerical chain appearing in Solution 1.

Each hypothesis corresponds to one equality obtained geometrically
from tangency, cyclic angles, or angle chasing.
-/
theorem arc_ML_eq_arc_MK
    (arcML arcMA arcKC arcMK
      angAKL angCPK angABL angKPS angPCS : ℝ)
    (hML :
      arcML = arcMA + 2 * angAKL)
    (hMA :
      arcMA = 2 * angCPK - arcKC)
    (hABL :
      angABL = angKPS)
    (hAKL :
      angAKL = angABL)
    (hPCS :
      angPCS = angCPK + angKPS)
    (hMK :
      arcMK = 2 * angPCS - arcKC) :
    arcML = arcMK := by

  calc
    arcML
        = arcMA + 2 * angAKL := hML

    _ =
      (2 * angCPK - arcKC) +
        2 * angAKL := by
          rw [hMA]

    _ =
      (2 * angCPK - arcKC) +
        2 * angABL := by
          rw [hAKL]

    _ =
      (2 * angCPK - arcKC) +
        2 * angKPS := by
          rw [hABL]

    _ =
      2 * (angCPK + angKPS) -
        arcKC := by
          ring

    _ =
      2 * angPCS - arcKC := by
          rw [← hPCS]

    _ = arcMK := hMK.symm

/-!
## Equal arcs give equal chords
-/

/--
We abstract the standard circle fact that chord length depends only
on the measure of the subtended minor arc.

For one fixed circle, `chord : ℝ → ℝ` maps an arc measure to its
corresponding chord length.
-/
lemma equal_chords_of_equal_arcs
    (chord : ℝ → ℝ)
    {α β : ℝ}
    (h : α = β) :
    chord α = chord β := by
  rw [h]

/--
Final metric form of the argument.

`chord arcML` represents `ML` and
`chord arcMK` represents `MK`.
-/
theorem imo2010_p4_arc_core
    (chord : ℝ → ℝ)
    (arcML arcMA arcKC arcMK
      angAKL angCPK angABL angKPS angPCS : ℝ)
    (hML :
      arcML = arcMA + 2 * angAKL)
    (hMA :
      arcMA = 2 * angCPK - arcKC)
    (hABL :
      angABL = angKPS)
    (hAKL :
      angAKL = angABL)
    (hPCS :
      angPCS = angCPK + angKPS)
    (hMK :
      arcMK = 2 * angPCS - arcKC) :
    chord arcMK = chord arcML := by

  have harc :
      arcML = arcMK := by
    exact
      arc_ML_eq_arc_MK
        arcML arcMA arcKC arcMK
        angAKL angCPK angABL angKPS angPCS
        hML hMA hABL hAKL hPCS hMK

  exact congrArg chord harc.symm

/-!
## Direct length formulation

The following packages the final standard Euclidean fact
"equal arcs of the same circle have equal chords" as the two
identifications of chord length.
-/
