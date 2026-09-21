by
  constructor
  · rintro ⟨m, hm, huniq⟩
    rcases Nat.lt_or_ge n 4 with h | h
    · rw [show n = 3 by omega] at hm
      exact absurd hm (not_consecLcmProp_three m)
    rcases Nat.lt_or_ge n 5 with h5 | h5
    · omega
    · exfalso
      obtain ⟨t, rfl⟩ : ∃ t, n = t + 5 := ⟨n - 5, by omega⟩
      have hco1 : Nat.Coprime (t + 4) (t + 3) := by
        show Nat.Coprime (t + 3 + 1) (t + 3); simp [Nat.Coprime]
      have hco2 : Nat.Coprime (t + 3) (t + 2) := by
        show Nat.Coprime (t + 2 + 1) (t + 2); simp [Nat.Coprime]
      have h1 : ConsecLcmProp (t + 5) ((t + 4) * (t + 2)) := by
        have := consecLcmProp_of_coprime (N := t + 4) (a := t + 4) (b := t + 3)
          (m := (t + 4) * (t + 2)) (by omega) (by omega) hco1 (by omega) (by omega) (by ring)
          (by positivity)
        simpa using this
      have h2 : ConsecLcmProp (t + 5) (t * t + 4 * t + 2) := by
        have := consecLcmProp_of_coprime (N := t + 4) (a := t + 3) (b := t + 2)
          (m := t * t + 4 * t + 2) (by omega) (by omega) hco2 (by omega) (by omega) (by ring)
          (by positivity)
        simpa using this
      have e1 := huniq _ h1
      have e2 := huniq _ h2
      nlinarith [e1, e2]
  · rintro rfl
    exact ⟨3, (consecLcmProp_four_iff 3).mpr rfl, fun m hm => (consecLcmProp_four_iff m).mp hm⟩
