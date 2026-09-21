by
  refine ⟨Set.range f, Set.infinite_range_of_injective f_inj, ?_, ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact ⟨K n, by have := (inv n).1; omega, f_def n⟩
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
    have hij : i ≠ j := fun hh => hne (by rw [hh])
    rcases Nat.lt_or_ge i j with h | h
    · exact coprime_lt h
    · exact (coprime_lt (by omega : j < i)).symm
