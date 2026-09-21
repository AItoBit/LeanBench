by
  rw [← coe_solSet hP, Set.ncard_coe_finset]
  by_cases h1 : ∃ a : ℤ, P.eval a = 1
  · by_cases h2 : ∃ b : ℤ, P.eval b = -1
    · obtain ⟨a, ha⟩ := h1
      obtain ⟨b, hb⟩ := h2
      rcases Nat.lt_or_ge P.natDegree 3 with hd | hd
      · exact le_trans (card_solSet_le_two_mul P) (by omega)
      · exact le_trans (card_solSet_le_five hP ha hb) (by omega)
    · push_neg at h2
      exact le_trans (card_solSet_le_of_no_neg_one hP h2) (by omega)
  · push_neg at h1
    exact le_trans (card_solSet_le_of_no_one hP h1) (by omega)
