by
  split_ifs with hp
  · ext x
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact (imo_1963_p1_forward p x h1 h2 h3).2.2
    · intro hx
      exact imo_1963_p1_backward p hp.1 hp.2 x hx
  · ext x
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h1, h2, h3⟩
    obtain ⟨ha, hb, -⟩ := imo_1963_p1_forward p x h1 h2 h3
    exact hp ⟨ha, hb⟩
