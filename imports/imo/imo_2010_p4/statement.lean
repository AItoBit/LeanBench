/--
If the geometric angle chase establishes equal arcs and the two
lengths are the chords corresponding to those arcs, then `MK = ML`.
-/
theorem candidate
    (chord : ℝ → ℝ)
    (MK ML : ℝ)
    (arcML arcMA arcKC arcMK
      angAKL angCPK angABL angKPS angPCS : ℝ)
    (hMKlen :
      MK = chord arcMK)
    (hMLlen :
      ML = chord arcML)
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
    MK = ML :=
