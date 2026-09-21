/-- The heart of the problem: for `x = k + 3` and `y > 0` the only solution is `k = 1`, `y = 23`. -/
theorem key (k : ℕ) (y : ℤ) (hy : 0 < y)
    (h : 1 + 8 * 2 ^ k + 128 * ((2 : ℤ) ^ k) ^ 2 = y ^ 2) : k = 1 ∧ y = 23 := by
  have hPpos : (0 : ℤ) < 2 ^ k := by positivity
  have hP1 : (1 : ℤ) ≤ 2 ^ k := by omega
  -- `y` is odd
  have hyo : y % 2 = 1 := by
    rcases Int.emod_two_eq_zero_or_one y with he | ho
    · exfalso
      obtain ⟨c, hc⟩ : ∃ c, y = 2 * c := ⟨y / 2, by omega⟩
      obtain ⟨d, hd⟩ : ∃ d, (1 : ℤ) = 4 * d :=
        ⟨c ^ 2 - 2 * 2 ^ k - 32 * ((2 : ℤ) ^ k) ^ 2, by rw [hc] at h; linear_combination h⟩
      omega
    · exact ho
  obtain ⟨a, ha⟩ : ∃ a, y = 2 * a + 1 := ⟨y / 2, by omega⟩
  have hfac : a * (a + 1) = 2 * 2 ^ k * (1 + 16 * 2 ^ k) := by
    have h4 : 4 * (a * (a + 1)) = 4 * (2 * 2 ^ k * (1 + 16 * 2 ^ k)) := by
      rw [ha] at h; linear_combination -h
    linarith
  rcases Int.emod_two_eq_zero_or_one a with hae | hao
  · -- `a` even: `y = 4Pc + 1`
    exfalso
    obtain ⟨b, hb⟩ : ∃ b, a = 2 * b := ⟨a / 2, by omega⟩
    have hb2 : b * (2 * b + 1) = 2 ^ k * (1 + 16 * 2 ^ k) := by
      have h2 : 2 * (b * (2 * b + 1)) = 2 * (2 ^ k * (1 + 16 * 2 ^ k)) := by
        rw [hb] at hfac; linear_combination hfac
      linarith
    have hcop : IsCoprime ((2 : ℤ) ^ k) (2 * b + 1) := IsCoprime.pow_left ⟨-b, 1, by ring⟩
    obtain ⟨c, hc⟩ : (2 : ℤ) ^ k ∣ b := hcop.dvd_of_dvd_mul_right ⟨1 + 16 * 2 ^ k, hb2⟩
    have hy4 : y = 4 * 2 ^ k * c + 1 := by rw [ha, hb, hc]; ring
    have heq2 : 1 + 16 * 2 ^ k = 2 * 2 ^ k * c ^ 2 + c := by
      refine mul_left_cancel₀ (a := (8 : ℤ) * 2 ^ k) (by positivity) ?_
      rw [hy4] at h; linear_combination h
    have hkey : 2 * 2 ^ k * (c ^ 2 - 8) = 1 - c := by linarith
    -- `c ≥ 1`
    have hc1 : 1 ≤ c := by
      by_contra hcon
      have hc0 : c ≤ 0 := by omega
      have hle : y ≤ 1 := by rw [hy4]; nlinarith
      have hy1 : y = 1 := by omega
      rw [hy1] at h
      nlinarith
    have hc2 : c ≤ 2 := by nlinarith
    interval_cases c <;> linarith
  · -- `a` odd: `y = 4Pc - 1`
    obtain ⟨t, ht⟩ : ∃ t, a = 2 * t + 1 := ⟨a / 2, by omega⟩
    have hb2 : (2 * t + 1) * (t + 1) = 2 ^ k * (1 + 16 * 2 ^ k) := by
      have h2 : 2 * ((2 * t + 1) * (t + 1)) = 2 * (2 ^ k * (1 + 16 * 2 ^ k)) := by
        rw [ht] at hfac; linear_combination hfac
      linarith
    have hcop : IsCoprime ((2 : ℤ) ^ k) (2 * t + 1) := IsCoprime.pow_left ⟨-t, 1, by ring⟩
    obtain ⟨c, hc⟩ : (2 : ℤ) ^ k ∣ (t + 1) := hcop.dvd_of_dvd_mul_left ⟨1 + 16 * 2 ^ k, hb2⟩
    have hy4 : y = 4 * 2 ^ k * c - 1 := by rw [ha, ht]; linarith
    have heq2 : 1 + 16 * 2 ^ k = 2 * 2 ^ k * c ^ 2 - c := by
      refine mul_left_cancel₀ (a := (8 : ℤ) * 2 ^ k) (by positivity) ?_
      rw [hy4] at h; linear_combination h
    have hkey : 2 * 2 ^ k * (c ^ 2 - 8) = 1 + c := by linarith
    have hc1 : 1 ≤ c := by nlinarith
    have hc3 : 3 ≤ c := by nlinarith
    have hc4 : c ≤ 3 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ 2 ^ k - 1) (by nlinarith : (0 : ℤ) ≤ c ^ 2 - 8)]
    have hce : c = 3 := by omega
    subst hce
    have hPe : (2 : ℤ) ^ k = 2 := by linarith
    have hk1 : k = 1 := by
      rcases Nat.lt_or_ge k 2 with hlt | hge
      · interval_cases k
        · exfalso; norm_num at hPe
        · rfl
      · exfalso
        have hnat : (4 : ℕ) ≤ 2 ^ k := by
          calc (4 : ℕ) = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hge
        have h4 : (4 : ℤ) ≤ (2 : ℤ) ^ k := by exact_mod_cast hnat
        linarith
    exact ⟨hk1, by rw [hy4, hPe]; ring⟩
