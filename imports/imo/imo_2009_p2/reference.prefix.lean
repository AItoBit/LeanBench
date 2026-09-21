namespace IMO2009P2

/--
The algebraic core of the proof of IMO 2009 Problem 2.

The variables denote the relevant (nonnegative) Euclidean lengths.

* `R`  : circumradius of `ABC`
* `OP` : distance `OP`
* `OQ` : distance `OQ`
* `QB`, `AQ`, `AP`, `PC`, `MK`, `ML` : the corresponding segment lengths

The hypotheses are precisely the metric equalities derived from
midpoints, similarity, and power of a point in the published proof.
-/
theorem imo2009_p2_metric
    (R OP OQ QB AQ AP PC MK ML : ℝ)
    (hOP : 0 ≤ OP)
    (hOQ : 0 ≤ OQ)
    (hpowQ :
      R ^ 2 - OQ ^ 2 = QB * AQ)
    (hQB :
      QB = 2 * MK)
    (hsim :
      AQ * MK = AP * ML)
    (hPC :
      PC = 2 * ML)
    (hpowP :
      AP * PC = R ^ 2 - OP ^ 2) :
    OP = OQ := by

  have h₁ :
      R ^ 2 - OQ ^ 2 =
        2 * AQ * MK := by
    calc
      R ^ 2 - OQ ^ 2
          = QB * AQ := hpowQ

      _ = (2 * MK) * AQ := by
            rw [hQB]

      _ = 2 * AQ * MK := by
            ring

  have h₂ :
      2 * AQ * MK =
        2 * AP * ML := by
    calc
      2 * AQ * MK
          = 2 * (AQ * MK) := by
              ring

      _ = 2 * (AP * ML) := by
              rw [hsim]

      _ = 2 * AP * ML := by
              ring

  have h₃ :
      2 * AP * ML =
        AP * PC := by
    rw [hPC]
    ring

  have hchain :
      R ^ 2 - OQ ^ 2 =
        R ^ 2 - OP ^ 2 := by
    calc
      R ^ 2 - OQ ^ 2
          = 2 * AQ * MK := h₁

      _ = 2 * AP * ML := h₂

      _ = AP * PC := h₃

      _ = R ^ 2 - OP ^ 2 := hpowP

  have hsquares :
      OP ^ 2 = OQ ^ 2 := by
    linarith

  nlinarith

/-!
A slightly more compact version, useful if the intermediate geometric
chain has already been established.
-/

/--
If the power identities on `P` and `Q` have the same middle value,
then the distances from the circumcenter are equal.
-/
lemma eq_dist_of_equal_powers
    (R OP OQ X : ℝ)
    (hOP : 0 ≤ OP)
    (hOQ : 0 ≤ OQ)
    (hQ : R ^ 2 - OQ ^ 2 = X)
    (hP : X = R ^ 2 - OP ^ 2) :
    OP = OQ := by

  have hsq :
      OP ^ 2 = OQ ^ 2 := by
    linarith

  nlinarith
