lemma eq_of_dvd_sub_of_lt
    {a b c : ℤ}
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (hab : a < b)
    (hcb : c < b)
    (hdiv : b ∣ a - c) :
    a = c := by

  rcases hdiv with ⟨q, hq⟩

  rcases lt_trichotomy q 0 with hqneg | hqzero | hqpos

  /- q < 0 -/
  · have hqle :
        q ≤ -1 := by
      omega

    have hmul :
        b * q ≤ b * (-1) := by
      exact
        mul_le_mul_of_nonneg_left
          hqle
          (le_of_lt hb)

    have hlower :
        -b < a - c := by
      linarith

    have hupper :
        a - c ≤ -b := by
      calc
        a - c = b * q := hq
        _ ≤ b * (-1) := hmul
        _ = -b := by ring

    linarith

  /- q = 0 -/
  · rw [hqzero] at hq
    simp at hq
    linarith

  /- q > 0 -/
  · have hqge :
        1 ≤ q := by
      omega

    have hmul :
        b ≤ b * q := by
      have h :=
        mul_le_mul_of_nonneg_left
          hqge
          (le_of_lt hb)

      simpa using h

    have hupper :
        a - c < b := by
      linarith

    have hlower :
        b ≤ a - c := by
      calc
        b ≤ b * q := hmul
        _ = a - c := hq.symm

    linarith

/-!
## Main theorem
-/
