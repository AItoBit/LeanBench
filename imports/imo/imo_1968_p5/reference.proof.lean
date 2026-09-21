by
  set quads := (S.powersetCard 4).filter InConvexPosition with hquads
  have hdc : (S.powersetCard 5).card * 1 ≤ quads.card * (S.card - 4) := by
    refine Finset.card_mul_le_card_mul (fun T Q => Q ⊆ T) ?_ ?_
    · intro T hT
      rw [Finset.mem_powersetCard] at hT
      have hgenT : NoThreeCollinear T := by
        intro a ha b hb c hc hab hac hbc
        exact hgen a (hT.1 ha) b (hT.1 hb) c (hT.1 hc) hab hac hbc
      obtain ⟨Q, hQT, hQcard, hQconv⟩ := exists_convex_quadrilateral hT.2 hgenT
      rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos]
      refine ⟨Q, ?_⟩
      rw [Finset.mem_bipartiteAbove]
      refine ⟨?_, hQT⟩
      rw [hquads, Finset.mem_filter, Finset.mem_powersetCard]
      exact ⟨⟨hQT.trans hT.1, hQcard⟩, hQconv⟩
    · intro Q hQ
      rw [hquads, Finset.mem_filter, Finset.mem_powersetCard] at hQ
      obtain ⟨⟨hQS, hQcard⟩, -⟩ := hQ
      have hle : (Finset.bipartiteBelow (fun T Q => Q ⊆ T) (S.powersetCard 5) Q).card ≤
          ((S \ Q).powersetCard 1).card := by
        refine Finset.card_le_card_of_injOn (fun T => T \ Q) ?_ ?_
        · intro T hT
          simp only [Finset.mem_coe] at hT
          rw [Finset.mem_bipartiteBelow, Finset.mem_powersetCard] at hT
          obtain ⟨⟨hTS, hTcard⟩, hQT⟩ := hT
          simp only [Finset.mem_coe, Finset.mem_powersetCard]
          refine ⟨Finset.sdiff_subset_sdiff hTS (le_refl Q), ?_⟩
          rw [Finset.card_sdiff_of_subset hQT, hTcard, hQcard]
        · intro T1 h1 T2 h2 heq
          simp only [Finset.mem_coe] at h1 h2
          rw [Finset.mem_bipartiteBelow] at h1 h2
          have e1 := Finset.union_sdiff_of_subset h1.2
          have e2 := Finset.union_sdiff_of_subset h2.2
          simp only at heq
          rw [← e1, ← e2, heq]
      calc (Finset.bipartiteBelow (fun T Q => Q ⊆ T) (S.powersetCard 5) Q).card
          ≤ ((S \ Q).powersetCard 1).card := hle
        _ = S.card - 4 := by
            rw [Finset.card_powersetCard, Finset.card_sdiff_of_subset hQS, hQcard,
              Nat.choose_one_right]
  rw [Finset.card_powersetCard, mul_one] at hdc
  have hb := choose_bound S.card hcard
  have hpos : 0 < S.card - 4 := by omega
  exact Nat.le_of_mul_le_mul_right (le_trans hb hdc) hpos

/-! ### Sanity checks on the notion of convex position -/
