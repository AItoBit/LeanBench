by
  classical
  have hn2 : n % 2 = 0 := Nat.even_iff.1 hn
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
  have hm : 0 < m := by omega
  have hval : 2 * m * (2 * m + 2) / 4 = m * (m + 1) := by
    rw [show 2 * m * (2 * m + 2) = 4 * (m * (m + 1)) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
  rw [hval]
  constructor
  · refine ⟨Qset (2 * m), Qset_subset_board, card_Qset hm, ?_⟩
    intro c hc
    obtain ⟨d, ⟨hdQ, hadj⟩, -⟩ := key hn2 hc
    exact ⟨d, hdQ, hadj⟩
  · rintro k ⟨S, hSb, rfl, hS⟩
    rw [← card_Qset hm]
    have hex : ∀ q ∈ Qset (2 * m), ∃ s ∈ S, Adj q s := fun q hq => hS q (Qset_subset_board hq)
    choose! f hfS hfAdj using hex
    refine Finset.card_le_card_of_injOn f hfS ?_
    intro q1 h1 q2 h2 heq
    rw [Finset.mem_coe] at h1 h2
    have hs : f q1 ∈ board (2 * m) := hSb (hfS q1 h1)
    obtain ⟨d, -, hd⟩ := key hn2 hs
    have e1 : q1 = d := hd q1 ⟨h1, adj_symm (hfAdj q1 h1)⟩
    have e2 : q2 = d := hd q2 ⟨h2, by rw [heq]; exact adj_symm (hfAdj q2 h2)⟩
    rw [e1, e2]
