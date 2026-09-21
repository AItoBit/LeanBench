by
  classical
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have key : ∀ p q r : Fin n, p ≠ q → p ≠ r → q ≠ r → t r < t p + t q := by
    intro p q r hpq hpr hqr
    by_contra hcon
    push Not at hcon
    set s : Finset (Fin n) := {p, q, r} with hs
    have hsub : s ⊆ Finset.univ := Finset.subset_univ _
    have hpm : p ∉ ({q, r} : Finset (Fin n)) := by simp [hpq, hpr]
    have hqm : q ∉ ({r} : Finset (Fin n)) := by simp [hqr]
    have hcard : s.card = 3 := by
      rw [hs, Finset.card_insert_of_notMem hpm, Finset.card_insert_of_notMem hqm,
        Finset.card_singleton]
    have hsumt : ∑ x ∈ s, t x = t p + t q + t r := by
      rw [hs, Finset.sum_insert hpm, Finset.sum_insert hqm, Finset.sum_singleton]
      ring
    have hsumi : ∑ x ∈ s, 1 / t x = 1 / t p + 1 / t q + 1 / t r := by
      rw [hs, Finset.sum_insert hpm, Finset.sum_insert hqm, Finset.sum_singleton]
      ring
    have hcard' : (Finset.univ \ s).card = n - 3 := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hcard]
    have hcast : (((n - 3 : ℕ)) : ℝ) = (n : ℝ) - 3 := by
      rw [Nat.cast_sub hn]
      norm_num
    have hsplit1 : (∑ x, t x) = (t p + t q + t r) + ∑ x ∈ Finset.univ \ s, t x := by
      rw [← Finset.sum_sdiff hsub, hsumt]
      ring
    have hsplit2 : (∑ x, 1 / t x)
        = (1 / t p + 1 / t q + 1 / t r) + ∑ x ∈ Finset.univ \ s, 1 / t x := by
      rw [← Finset.sum_sdiff hsub, hsumi]
      ring
    have hXY : 10 ≤ (t p + t q + t r) * (1 / t p + 1 / t q + 1 / t r) :=
      three_bound (ht p) (ht q) (ht r) hcon
    have hRU : ((n : ℝ) - 3) ^ 2
        ≤ (∑ x ∈ Finset.univ \ s, t x) * (∑ x ∈ Finset.univ \ s, 1 / t x) := by
      have h1 := card_sq_le t (Finset.univ \ s) (fun x _ => ht x)
      rwa [hcard', hcast] at h1
    have hR0 : 0 ≤ ∑ x ∈ Finset.univ \ s, t x :=
      Finset.sum_nonneg fun x _ => (ht x).le
    have hU0 : 0 ≤ ∑ x ∈ Finset.univ \ s, 1 / t x :=
      Finset.sum_nonneg fun x _ => (one_div_pos.2 (ht x)).le
    have hX0 : 0 < t p + t q + t r := by
      have := ht p; have := ht q; have := ht r; linarith
    have hY0 : 0 < 1 / t p + 1 / t q + 1 / t r := by
      have := one_div_pos.2 (ht p); have := one_div_pos.2 (ht q); have := one_div_pos.2 (ht r)
      linarith
    have hm0 : (0 : ℝ) ≤ (n : ℝ) - 3 := by linarith
    have hcross : 6 * ((n : ℝ) - 3)
        ≤ (t p + t q + t r) * (∑ x ∈ Finset.univ \ s, 1 / t x)
          + (∑ x ∈ Finset.univ \ s, t x) * (1 / t p + 1 / t q + 1 / t r) := by
      have hnn : 0 ≤ (t p + t q + t r) * (∑ x ∈ Finset.univ \ s, 1 / t x)
          + (∑ x ∈ Finset.univ \ s, t x) * (1 / t p + 1 / t q + 1 / t r) := by positivity
      have hbig : 10 * ((n : ℝ) - 3) ^ 2
          ≤ ((t p + t q + t r) * (1 / t p + 1 / t q + 1 / t r))
            * ((∑ x ∈ Finset.univ \ s, t x) * (∑ x ∈ Finset.univ \ s, 1 / t x)) := by
        nlinarith [hXY, hRU, sq_nonneg ((n : ℝ) - 3), mul_nonneg hR0 hU0]
      nlinarith [sq_nonneg ((t p + t q + t r) * (∑ x ∈ Finset.univ \ s, 1 / t x)
          - (∑ x ∈ Finset.univ \ s, t x) * (1 / t p + 1 / t q + 1 / t r)),
        hbig, hnn, hm0]
    have hfinal : (n : ℝ) ^ 2 + 1 ≤ (∑ x, t x) * (∑ x, 1 / t x) := by
      rw [hsplit1, hsplit2]
      nlinarith [hXY, hRU, hcross]
    linarith
  have hij' : i ≠ j := ne_of_lt hij
  have hjk' : j ≠ k := ne_of_lt hjk
  have hik' : i ≠ k := ne_of_lt (lt_trans hij hjk)
  exact ⟨key i j k hij' hik' hjk',
    key j k i hjk' (Ne.symm hij') (Ne.symm hik'),
    key i k j hik' hij' (Ne.symm hjk')⟩
