by
  ext n
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hlen, hdvd, hsum⟩
    have hn : n < 1000 := by
      have := (Nat.digits_length_le_iff (b := 10) (k := 3) (by norm_num) n).mp hlen.le
      simpa using this
    exact (imo_1960_p1_bounded n (Finset.mem_range.mpr hn)).mp ⟨hlen, hdvd, hsum⟩
  · rintro (rfl | rfl)
    · exact (imo_1960_p1_bounded 550 (by decide)).mpr (Or.inl rfl)
    · exact (imo_1960_p1_bounded 803 (by decide)).mpr (Or.inr rfl)
