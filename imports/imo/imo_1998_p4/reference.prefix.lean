namespace IMO1998P4

lemma classify_int (a b : ℤ) (ha : 0 < a) (hb : 0 < b)
    (hd : a * b ^ 2 + b + 7 ∣ a ^ 2 * b + a + b) :
    7 * a = b ^ 2 ∨ (b = 1 ∧ (a = 11 ∨ a = 49)) := by
  obtain ⟨c, hc⟩ := hd
  let D := a * b ^ 2 + b + 7
  let q := a - b * c

  have hD : 0 < D := by
    dsimp [D]
    nlinarith [mul_pos ha (sq_pos_of_pos hb)]

  have hq : D * q = 7 * a - b ^ 2 := by
    dsimp [D, q]
    linear_combination b * hc

  have hbase : b ^ 2 < D := by
    dsimp [D]
    have h :=
      mul_nonneg (show 0 ≤ a - 1 by omega) (sq_nonneg b)
    nlinarith

  have hqnonneg : 0 ≤ q := by
    by_contra hn
    have hq1 : q ≤ -1 :=
      Int.le_sub_one_of_lt (lt_of_not_ge hn)
    have hmul :=
      mul_nonpos_of_nonneg_of_nonpos
        (le_of_lt hD) (show q + 1 ≤ 0 by omega)
    nlinarith

  by_cases hq0 : q = 0
  · left
    rw [hq0, mul_zero] at hq
    linarith
  · right
    have hqpos : 1 ≤ q := by omega

    have hbound : D ≤ 7 * a - b ^ 2 := by
      have hmul :=
        mul_nonneg (le_of_lt hD) (show 0 ≤ q - 1 by omega)
      nlinarith

    have hb2 : b ≤ 2 := by
      by_contra hn
      have hb3 : 3 ≤ b :=
        Int.add_one_le_iff.mpr (lt_of_not_ge hn)
      have hs : 0 ≤ b ^ 2 - 9 := by nlinarith
      have hm := mul_nonneg (le_of_lt ha) hs
      dsimp [D] at hbound
      nlinarith

    have hcases : b = 1 ∨ b = 2 := by omega
    rcases hcases with rfl | rfl

    · refine ⟨rfl, ?_⟩
      let t := 7 - q

      have ht : (a + 8) * t = 57 := by
        dsimp [D] at hq
        dsimp [t]
        nlinarith [hq]

      have htpos : 0 < t := by
        by_contra hn
        have hm :=
          mul_nonpos_of_nonneg_of_nonpos
            (show 0 ≤ a + 8 by omega) (le_of_not_gt hn)
        nlinarith

      have ht6 : t ≤ 6 := by
        have hm :=
          mul_nonneg (show 0 ≤ a - 1 by omega) (le_of_lt htpos)
        nlinarith

      interval_cases t <;> omega

    · exfalso
      let t := 7 - 4 * q

      have ht : (4 * a + 9) * t = 79 := by
        dsimp [D] at hq
        dsimp [t]
        nlinarith [hq]

      have htpos : 0 < t := by
        by_contra hn
        have hm :=
          mul_nonpos_of_nonneg_of_nonpos
            (show 0 ≤ 4 * a + 9 by omega) (le_of_not_gt hn)
        nlinarith

      have ht6 : t ≤ 6 := by
        have hm :=
          mul_nonneg (show 0 ≤ a - 1 by omega) (le_of_lt htpos)
        nlinarith

      interval_cases t <;> omega
