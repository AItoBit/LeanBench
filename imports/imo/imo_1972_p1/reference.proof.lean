by
  classical
  -- every subset sum is at most `10 * 99 = 990`
  have hmaps : ∀ T ∈ S.powerset, (∑ x ∈ T, x) ∈ Finset.range 991 := by
    intro T hT
    rw [Finset.mem_powerset] at hT
    rw [Finset.mem_range]
    have h1 : ∑ x ∈ T, x ≤ T.card * 99 := by
      have h := Finset.sum_le_card_nsmul T (fun x => x) 99 fun x hx => (hS x (hT hx)).2
      simpa [smul_eq_mul] using h
    have h2 : T.card ≤ 10 := by
      rw [← hcard]; exact Finset.card_le_card hT
    omega
  -- there are more subsets than possible sums
  have hlt : (Finset.range 991).card < S.powerset.card := by
    rw [Finset.card_range, Finset.card_powerset, hcard]
    norm_num
  obtain ⟨A, hAmem, B, hBmem, hne, hsum⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  rw [Finset.mem_powerset] at hAmem hBmem
  refine ⟨A \ B, B \ A, Finset.sdiff_subset.trans hAmem, Finset.sdiff_subset.trans hBmem,
    nonempty_sdiff hS hAmem hBmem hne hsum,
    nonempty_sdiff hS hBmem hAmem (Ne.symm hne) hsum.symm, ?_, ?_⟩
  · -- disjointness
    rw [Finset.disjoint_left]
    intro a ha hb
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mp hb).1
  · -- equal sums
    have h1 : ∑ x ∈ A \ B, x + ∑ x ∈ A ∩ B, x = ∑ x ∈ A, x := sum_split A B
    have h2 : ∑ x ∈ B \ A, x + ∑ x ∈ B ∩ A, x = ∑ x ∈ B, x := sum_split B A
    have h3 : B ∩ A = A ∩ B := Finset.inter_comm B A
    rw [h3] at h2
    omega
