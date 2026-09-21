by
  constructor
  · -- `(m, n) = (3, 103)`
    exact ⟨3, 103, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · rintro s ⟨m, n, hm, hmn, heq, rfl⟩
    obtain ⟨d, hd1, rfl⟩ : ∃ d, 1 ≤ d ∧ n = m + d := ⟨n - m, by omega, by omega⟩
    have hmod : 1978 ^ m ≡ 1978 ^ (m + d) [MOD 1000] := heq
    -- the `2`-part: `m ≥ 3`
    have hm3 : 3 ≤ m := by
      by_contra hcon
      have hm2 : m ≤ 2 := by omega
      have h8eq : 1978 ^ m ≡ 1978 ^ (m + d) [MOD 8] :=
        Nat.ModEq.of_dvd (by norm_num) hmod
      interval_cases m
      · have h4 : 4 ∣ 1978 ^ (1 + d) := dvd4 _ (by omega)
        have e1 : 1978 ^ 1 % 8 = 2 := by norm_num
        have h8eq' : 1978 ^ 1 % 8 = 1978 ^ (1 + d) % 8 := h8eq
        omega
      · have h8 : 8 ∣ 1978 ^ (2 + d) := dvd8 _ (by omega)
        have e2 : 1978 ^ 2 % 8 = 4 := by norm_num
        have h8eq' : 1978 ^ 2 % 8 = 1978 ^ (2 + d) % 8 := h8eq
        omega
    -- the `5`-part: `d ≥ 100`
    have h125 : 1978 ^ m ≡ 1978 ^ (m + d) [MOD 125] :=
      Nat.ModEq.of_dvd (by norm_num) hmod
    rw [pow_add] at h125
    have hcop : Nat.gcd 125 (1978 ^ m) = 1 :=
      Nat.Coprime.pow_right m (by norm_num)
    have hcancel : (1 : ℕ) ≡ 1978 ^ d [MOD 125] := by
      refine Nat.ModEq.cancel_left_of_coprime hcop ?_
      simpa using h125
    have hdvd : 100 ∣ d := order_125 hcancel.symm
    have hd100 : 100 ≤ d := Nat.le_of_dvd (by omega) hdvd
    omega
