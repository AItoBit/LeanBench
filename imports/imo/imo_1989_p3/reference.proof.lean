by
  classical
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  -- The finset of "isosceles" ordered triples.
  obtain ⟨E, hE⟩ : ∃ E : Finset (Pt × Pt × Pt), ∀ t : Pt × Pt × Pt, t ∈ E ↔
      (t.1 ∈ S ∧ t.2.1 ∈ S ∧ t.2.2 ∈ S ∧ t.2.1 ≠ t.2.2 ∧ t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧
        dist t.1 t.2.1 = dist t.1 t.2.2) := by
    refine ⟨{t ∈ S ×ˢ S ×ˢ S | t.2.1 ≠ t.2.2 ∧ t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧
      dist t.1 t.2.1 = dist t.1 t.2.2}, fun t => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_product]
    tauto
  -- Lower bound.
  have hlow : (m + 1) * ((j + 1) * j) ≤ E.card := by
    have hmaps : Set.MapsTo (fun t : Pt × Pt × Pt => t.1) (E : Set (Pt × Pt × Pt))
        (S : Set Pt) := by
      intro t ht
      rw [Finset.mem_coe, hE] at ht
      exact Finset.mem_coe.2 ht.1
    rw [Finset.card_eq_sum_card_fiberwise hmaps, show m + 1 = S.card from hS.symm,
      ← smul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun a ha => ?_
    obtain ⟨T, hTsub, hTcard, d, hd⟩ := hequi a ha
    have hcard : (j + 1) * j ≤ T.offDiag.card := by
      obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hTcard
      rw [Finset.offDiag_card, he]
      have hexp : (j + 1 + e) * (j + 1 + e)
          = (j + 1) * j + (j + 1 + e) + (e * e + 2 * j * e + e) := by ring
      refine Nat.le_sub_of_add_le ?_
      rw [hexp]
      exact Nat.le_add_right _ _
    refine le_trans hcard (Finset.card_le_card_of_injOn (s := T.offDiag)
      (fun p : Pt × Pt => (a, p.1, p.2)) ?_ ?_)
    · intro p hp
      rw [Finset.mem_coe, Finset.mem_offDiag] at hp
      obtain ⟨hp1, hp2, hp12⟩ := hp
      have hb := Finset.mem_erase.1 (hTsub hp1)
      have hc := Finset.mem_erase.1 (hTsub hp2)
      refine Finset.mem_coe.2 (Finset.mem_filter.2
        ⟨(hE _).2 ⟨ha, hb.2, hc.2, hp12, ?_, ?_, ?_⟩, rfl⟩)
      · exact fun h => hb.1 h.symm
      · exact fun h => hc.1 h.symm
      · rw [hd _ hp1, hd _ hp2]
    · intro p _ q _ h
      simpa [Prod.ext_iff] using h
  -- Upper bound.
  have hup : E.card ≤ 2 * ((m + 1) * m) := by
    have hmaps : Set.MapsTo (fun t : Pt × Pt × Pt => (t.2.1, t.2.2)) (E : Set (Pt × Pt × Pt))
        (S.offDiag : Set (Pt × Pt)) := by
      intro t ht
      rw [Finset.mem_coe, hE] at ht
      exact Finset.mem_coe.2 (Finset.mem_offDiag.2 ⟨ht.2.1, ht.2.2.1, ht.2.2.2.1⟩)
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    refine le_trans (Finset.sum_le_sum (g := fun _ => 2) fun p hp => ?_) ?_
    · -- at most two apices for a given base
      by_contra hcon
      rw [Nat.not_le] at hcon
      obtain ⟨U, hUsub, hU3⟩ := Finset.exists_subset_card_eq (show 3 ≤ _ from hcon)
      obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.1 hU3
      have hxm : x ∈ ({x, y, z} : Finset (Pt × Pt × Pt)) := by simp
      have hym : y ∈ ({x, y, z} : Finset (Pt × Pt × Pt)) := by simp
      have hzm : z ∈ ({x, y, z} : Finset (Pt × Pt × Pt)) := by simp
      have hx := Finset.mem_filter.1 (hUsub hxm)
      have hy := Finset.mem_filter.1 (hUsub hym)
      have hz := Finset.mem_filter.1 (hUsub hzm)
      obtain ⟨hx1, -, -, hxBC, -, -, hxd⟩ := (hE x).1 hx.1
      obtain ⟨hy1, -, -, -, -, -, hyd⟩ := (hE y).1 hy.1
      obtain ⟨hz1, -, -, -, -, -, hzd⟩ := (hE z).1 hz.1
      have hxy2 : x.2 = y.2 := by simpa [Prod.ext_iff] using hx.2.trans hy.2.symm
      have hxz2 : x.2 = z.2 := by simpa [Prod.ext_iff] using hx.2.trans hz.2.symm
      have hne₁ : x.1 ≠ y.1 := fun h => hxy (Prod.ext_iff.2 ⟨h, hxy2⟩)
      have hne₂ : x.1 ≠ z.1 := fun h => hxz (Prod.ext_iff.2 ⟨h, hxz2⟩)
      have hne₃ : y.1 ≠ z.1 := fun h => hyz (Prod.ext_iff.2 ⟨h, hxy2 ▸ hxz2⟩)
      refine hcol x.1 hx1 y.1 hy1 z.1 hz1 hne₁ hne₂ hne₃ ?_
      refine collinear_of_dist_eq hxBC hxd ?_ ?_
      · rw [hxy2]; exact hyd
      · rw [hxz2]; exact hzd
    · rw [Finset.sum_const, Finset.offDiag_card, hS, smul_eq_mul, mul_comm]
      have hoff : (m + 1) * (m + 1) - (m + 1) = (m + 1) * m := by
        rw [Nat.mul_add, Nat.mul_one, Nat.add_sub_cancel]
      rw [hoff]
  -- Combine and cancel the factor `n = m + 1`.
  have hcomb : (j + 1) * j ≤ 2 * m := by
    have h := le_trans hlow hup
    have h' : (m + 1) * ((j + 1) * j) ≤ (m + 1) * (2 * m) := by
      calc (m + 1) * ((j + 1) * j) ≤ 2 * ((m + 1) * m) := h
        _ = (m + 1) * (2 * m) := by ring
    exact Nat.le_of_mul_le_mul_left h' (Nat.succ_pos m)
  -- Finish over the reals.
  have hcast : ((j : ℝ) + 1) * j ≤ 2 * m := by exact_mod_cast hcomb
  by_contra hcontra
  rw [not_lt] at hcontra
  set s := Real.sqrt (2 * ((m : ℝ) + 1)) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 2 * ((m : ℝ) + 1) := Real.sq_sqrt (by positivity)
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hcontra' : 1 / 2 + s ≤ (j : ℝ) + 1 := by
    push_cast at hcontra
    simpa [hs] using hcontra
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (j : ℝ) + 1 / 2 - s)
    (by linarith : (0 : ℝ) ≤ (j : ℝ) + 1 / 2 + s)]
