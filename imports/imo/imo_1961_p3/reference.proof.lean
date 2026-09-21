by
  have hn0 : n ≠ 0 := h₀.ne'
  ext x
  simp only [Set.mem_ofPred_eq]
  rw [Imo1961Q3 hn0]
  split_ifs with hev
  · have hodd : ¬ Odd n := by simpa [Nat.not_odd_iff_even] using hev
    simp only [Set.mem_ofPred_eq, hev, hodd, and_true, and_false, or_false]
  · have hodd : Odd n := Nat.not_even_iff_odd.1 hev
    simp only [Set.mem_ofPred_eq, hev, hodd, and_true, and_false, false_or]
    constructor
    · rintro (⟨k, rfl⟩ | ⟨k, rfl⟩)
      · exact ⟨k, Or.inl (by ring)⟩
      · exact ⟨k, Or.inr (by ring)⟩
    · rintro ⟨k, rfl | rfl⟩
      · exact Or.inl ⟨k, by ring⟩
      · exact Or.inr ⟨k, by ring⟩
