by
  constructor
  · intro hdvd
    rcases Nat.lt_or_ge n 2 with h1 | hn2
    · exact Or.inl (by omega)
    rcases Nat.lt_or_ge p 3 with hp2 | hp3
    · have hpe : p = 2 := by have := hp.two_le; omega
      subst hpe
      refine Or.inr (Or.inl ⟨?_, rfl⟩)
      have hd : n ∣ 2 := by simpa using hdvd
      have := Nat.le_of_dvd (by omega) hd
      interval_cases n <;> simp_all
    · have hnodd : Odd n := by
        rcases Nat.even_or_odd n with he | ho
        · exfalso
          have h2n : (2 : ℕ) ∣ n := he.two_dvd
          have h2 : (2 : ℕ) ∣ (p - 1) ^ n + 1 :=
            dvd_trans (dvd_trans h2n (dvd_pow_self n (by omega))) hdvd
          have hpm : Even (p - 1) := by
            have hpo := hp.odd_of_ne_two (by omega)
            rw [Nat.odd_iff] at hpo
            rw [Nat.even_iff]
            omega
          have hevp : Even ((p - 1) ^ n) := Nat.even_pow.2 ⟨hpm, by omega⟩
          rw [Nat.even_iff] at hevp
          rw [Nat.dvd_iff_mod_eq_zero] at h2
          omega
        · exact ho
      have hpn : p ∣ n := p_dvd_n hp hp3 hn2 hnodd hdvd
      have hnp : n = p := by
        obtain ⟨c, hc⟩ := hpn
        have hc2 : c ≤ 2 := by
          by_contra hcon
          have : 3 * p ≤ n := by rw [hc]; nlinarith
          omega
        interval_cases c
        · omega
        · omega
        · exfalso
          rw [Nat.odd_iff] at hnodd
          have hpodd := hp.odd_of_ne_two (by omega)
          rw [Nat.odd_iff] at hpodd
          omega
      subst hnp
      have h3 := p_eq_three hp hp3 hdvd
      exact Or.inr (Or.inr ⟨h3, h3⟩)
  · rintro (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · simp
    · decide
    · decide
