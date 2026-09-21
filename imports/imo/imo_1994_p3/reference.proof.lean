by
  constructor
  · rintro ⟨k, ⟨hk0, hfk⟩, huniq⟩
    have hf1 : f 1 = 0 := by decide
    have hk2 : 2 ≤ k := by
      rcases (by omega : k = 1 ∨ 2 ≤ k) with rfl | h
      · omega
      · exact h
    have hones_k : onesCount k = 2 := by
      by_contra h
      have hs := f_succ k (by omega)
      rw [if_neg h] at hs
      have := huniq (k + 1) ⟨by omega, by omega⟩
      omega
    have hones_km : onesCount (k - 1) = 2 := by
      by_contra h
      have hs := f_succ (k - 1) (by omega)
      rw [if_neg h, show k - 1 + 1 = k by omega] at hs
      have := huniq (k - 1) ⟨by omega, by omega⟩
      omega
    obtain ⟨a, ha, hka⟩ := (consecutive_two_ones k hk2).mp ⟨hones_k, hones_km⟩
    exact ⟨a, ha, by rw [← hfk, hka, f_pow_add_two a ha]⟩
  · rintro ⟨n, hn, rfl⟩
    refine ⟨2 ^ n + 2, ⟨by positivity, f_pow_add_two n hn⟩, ?_⟩
    rintro j ⟨hj0, hfj⟩
    by_contra hne
    have hfval := f_pow_add_two n hn
    rcases (by omega : j < 2 ^ n + 2 ∨ 2 ^ n + 2 < j) with h | h
    · have hs := f_succ (2 ^ n + 1) (Nat.le_add_left 1 _)
      rw [show 2 ^ n + 1 + 1 = 2 ^ n + 2 by omega,
        if_pos (onesCount_pow_add_one n (by omega))] at hs
      have hmono : f j ≤ f (2 ^ n + 1) := f_mono (by omega)
      omega
    · have hs := f_succ (2 ^ n + 2) (Nat.le_add_left 1 _)
      rw [if_pos (onesCount_pow_add_two n hn)] at hs
      have hmono : f (2 ^ n + 2 + 1) ≤ f j := f_mono (by omega)
      omega
