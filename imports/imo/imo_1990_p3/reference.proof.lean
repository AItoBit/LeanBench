by
  constructor
  · intro h
    by_contra hne
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have hodd : Odd n := odd_of_dvd hn h
    have h3n : (3 : ℕ) ∣ n := by
      have := minFac_eq_three hn h
      exact this ▸ Nat.minFac_dvd n
    obtain ⟨m, hm⟩ := h3n
    have hv := padicValNat_three_eq_one hn h
    have h3m : ¬ (3 : ℕ) ∣ m := by
      intro ⟨k, hk⟩
      have h9 : (3 : ℕ) ^ 2 ∣ n := ⟨k, by rw [hm, hk]; ring⟩
      have : 2 ≤ padicValNat 3 n := (padicValNat_dvd_iff_le (by omega)).mp h9
      omega
    have hm1 : 1 < m := by
      rcases Nat.lt_or_ge m 2 with hlt | hge
      · interval_cases m <;> omega
      · omega
    set q := m.minFac with hq
    have hqp : q.Prime := Nat.minFac_prime (by omega)
    haveI : Fact q.Prime := ⟨hqp⟩
    have hqm : q ∣ m := Nat.minFac_dvd m
    have hqn : q ∣ n := hm ▸ Dvd.dvd.mul_left hqm 3
    have hqd : q ∣ 2 ^ n + 1 := dvd_trans hqn (dvd_trans (dvd_pow_self n two_ne_zero) h)
    have hq3 : q ≠ 3 := fun hc => h3m (hc ▸ hqm)
    have hd1 : orderOf (2 : ZMod q) ∣ 2 * n := orderOf_two_dvd_two_mul hqd
    have hq2 : q ≠ 2 := by
      intro h2
      have : (2 : ℕ) ∣ n := h2 ▸ hqn
      rcases hodd with ⟨k, hk⟩
      omega
    have hd2 : orderOf (2 : ZMod q) ∣ q - 1 := orderOf_two_dvd_sub_one hq2
    have hcop : Nat.Coprime m (q - 1) := by
      apply coprime_of_lt_minFac
      · have := hqp.two_le; omega
      · have := hqp.two_le; omega
    have hcop2 : Nat.Coprime (orderOf (2 : ZMod q)) m :=
      (Nat.Coprime.coprime_dvd_right hd2 hcop).symm
    have hd6 : orderOf (2 : ZMod q) ∣ 6 := by
      have h6m : orderOf (2 : ZMod q) ∣ 6 * m := by
        rw [show 6 * m = 2 * n by rw [hm]; ring]
        exact hd1
      exact hcop2.dvd_of_dvd_mul_right h6m
    have h63 : q ∣ 2 ^ 6 - 1 := dvd_two_pow_sub_one hd6
    norm_num at h63
    -- `63 = 7 * 9`, and `q ≠ 3`, so `q = 7`
    have hq9 : ¬ q ∣ 9 := by
      intro hdd
      have : q ∣ 3 ^ 2 := by norm_num at hdd ⊢; exact hdd
      have := hqp.dvd_of_dvd_pow this
      exact hq3 ((Nat.prime_dvd_prime_iff_eq hqp (by norm_num)).mp this)
    have hcq : Nat.Coprime q 9 := (Nat.Prime.coprime_iff_not_dvd hqp).mpr hq9
    have hq7 : q ∣ 7 := by
      have : q ∣ 7 * 9 := by norm_num; exact h63
      exact hcq.dvd_of_dvd_mul_right this
    have hq7' : q = 7 := (Nat.prime_dvd_prime_iff_eq hqp (by norm_num)).mp hq7
    -- but `7 ∣ 2 ^ n + 1` is impossible when `3 ∣ n`
    have h7 : (7 : ℕ) ∣ 2 ^ n + 1 := hq7' ▸ hqd
    have hpow : 2 ^ n % 7 = 1 := by
      have : (2 : ℕ) ^ n = 8 ^ (n / 3) := by
        rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul]
        congr 1
        omega
      rw [this]
      have : (8 : ℕ) ^ (n / 3) % 7 = 1 ^ (n / 3) % 7 := Nat.pow_mod 8 (n / 3) 7 ▸ by
        norm_num [Nat.pow_mod]
      simpa using this
    omega
  · rintro rfl
    norm_num
