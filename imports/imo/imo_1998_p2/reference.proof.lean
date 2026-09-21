by
  have hlower (i : Fin a) :
      (b : ℝ) ^ 2 + 1 ≤
        2 * (∑ j : Fin b, ∑ l : Fin b,
          agreement vote i j l) := by
    rw [row_count]
    exact odd_square_bound (split_count (vote i)) hodd

  have hlower_sum :=
    Finset.sum_le_sum
      (s := (Finset.univ : Finset (Fin a)))
      (fun i _ => hlower i)

  have hlower_total :
      (a : ℝ) * ((b : ℝ) ^ 2 + 1) ≤
        2 * (∑ i : Fin a, ∑ j : Fin b, ∑ l : Fin b,
          agreement vote i j l) := by
    simpa [← Finset.mul_sum, mul_add] using hlower_sum

  have hupper (j l : Fin b) :
      (∑ i : Fin a, agreement vote i j l) ≤
        (if l = j then (a : ℝ) - k else 0) + k := by
    by_cases h : l = j
    · subst l
      simp [agreement]
    · simpa [agreement, agreementCount, h] using
        hpair j l (Ne.symm h)

  have hupper_sum :=
    Finset.sum_le_sum
      (s := (Finset.univ : Finset (Fin b)))
      (fun j _ =>
        Finset.sum_le_sum
          (s := (Finset.univ : Finset (Fin b)))
          (fun l _ => hupper j l))

  have hupper_total :
      (∑ j : Fin b, ∑ l : Fin b, ∑ i : Fin a,
        agreement vote i j l) ≤
        (b : ℝ) * ((a : ℝ) - k + b * k) := by
    simpa [Finset.sum_add_distrib, mul_add] using hupper_sum

  have hswap :
      (∑ i : Fin a, ∑ j : Fin b, ∑ l : Fin b,
        agreement vote i j l) =
        ∑ j : Fin b, ∑ l : Fin b, ∑ i : Fin a,
          agreement vote i j l := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]

  rw [hswap] at hlower_total

  have hbR : (3 : ℝ) ≤ b := by
    exact_mod_cast hb
  have haR : (0 : ℝ) < a := by
    exact_mod_cast ha
  have hb1 : 0 < (b : ℝ) - 1 := by
    linarith

  have hprod :
      ((b : ℝ) - 1) * ((a : ℝ) * ((b : ℝ) - 1)) ≤
        ((b : ℝ) - 1) * (2 * (b : ℝ) * k) := by
    nlinarith [hlower_total, hupper_total]

  have hcore :
      (a : ℝ) * ((b : ℝ) - 1) ≤ 2 * (b : ℝ) * k := by
    by_contra h
    have hp :=
      mul_pos hb1 (sub_pos.mpr (lt_of_not_ge h))
    nlinarith [hprod]

  apply
    (div_le_div_iff₀
      (by linarith : (0 : ℝ) < 2 * b) haR).2
  nlinarith [hcore]
