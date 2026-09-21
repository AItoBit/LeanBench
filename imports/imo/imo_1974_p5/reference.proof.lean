by
  ext s
  simp only [Set.mem_setOf_eq, Set.mem_Ioo]
  constructor
  · rintro ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩
    exact ⟨one_lt_S ha hb hc hd, S_lt_two ha hb hc hd⟩
  · rintro ⟨h1, h2⟩
    rcases le_or_gt s (4 / 3) with hs | hs
    · obtain ⟨t, ht1, ht⟩ := exists_param (v := s - 1) (by linarith) (by linarith)
      have ht0 : 0 < t := by linarith
      exact ⟨1, t, t, 1, one_pos, ht0, ht0, one_pos, by
        rw [S_lower_family ht0, ht]; ring⟩
    · obtain ⟨t, ht1, ht⟩ := exists_param (v := (2 - s) / 2) (by linarith) (by linarith)
      have ht0 : 0 < t := by linarith
      exact ⟨t, 1, t, 1, ht0, one_pos, ht0, one_pos, by
        rw [S_upper_family ht0, ht]; ring⟩
