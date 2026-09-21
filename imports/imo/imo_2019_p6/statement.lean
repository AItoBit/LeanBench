/--
Complete logical skeleton of the source proof.

The substantial Euclidean/inversion facts are explicit
hypotheses rather than hidden behind `sorry`.
-/
theorem candidate
    {Ω : Circle}
    {A I D P Q M C E S X : Point}

    (hP :
      OnCircle Ω P)

    (hS :
      OnCircle Ω S)

    (hM :
      OnCircle Ω M)

    (hPQM_PQC :
      ang P Q M =
        ang P Q C)

    (hPQC_PEC :
      ang P Q C =
        ang P E C)

    (hPEC_PED :
      ang P E C =
        ang P E D)

    (hPED_PSD :
      ang P E D =
        ang P S D)

    (hPSD_PSM :
      ang P S D =
        ang P S M)

    (q_membership :
      OnCircle Ω P →
      OnCircle Ω S →
      OnCircle Ω M →
      ang P Q M =
          ang P S M →
      OnCircle Ω Q)

    (reduction :
      OnCircle Ω Q →
      Collinear D I X ∧
      Collinear P Q X ∧
      Perpendicular A X A I) :
    Target
      Collinear
      Perpendicular
      A I D P Q X :=
