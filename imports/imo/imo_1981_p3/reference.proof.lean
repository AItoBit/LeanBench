by
  constructor
  · exact ⟨987, 1597, by norm_num⟩
  · rintro s ⟨m, n, hm1, hm2, hn1, hn2, hmn, rfl⟩
    lift m to ℕ using (by linarith : (0 : ℤ) ≤ m) with M
    lift n to ℕ using (by linarith : (0 : ℤ) ≤ n) with N
    have hM1 : 1 ≤ M := by exact_mod_cast hm1
    have hN1 : 1 ≤ N := by exact_mod_cast hn1
    have hN2 : N ≤ 1981 := by exact_mod_cast hn2
    obtain ⟨k, hk1, hk2⟩ := solutions_are_fib (M + N) M N le_rfl hM1 hN1 hmn
    have hk : k ≤ 16 := fib_index_le k (by omega)
    have hb1 : Nat.fib k ≤ 987 := by
      have := Nat.fib_mono (show k ≤ 16 from hk)
      have h16 : Nat.fib 16 = 987 := by decide
      omega
    have hb2 : Nat.fib (k + 1) ≤ 1597 := by
      have := Nat.fib_mono (show k + 1 ≤ 17 by omega)
      have h17 : Nat.fib 17 = 1597 := by decide
      omega
    have hM : M ≤ 987 := by omega
    have hN : N ≤ 1597 := by omega
    have hM' : (M : ℤ) ≤ 987 := by exact_mod_cast hM
    have hN' : (N : ℤ) ≤ 1597 := by exact_mod_cast hN
    have hM0 : (0 : ℤ) ≤ (M : ℤ) := Int.natCast_nonneg M
    have hN0 : (0 : ℤ) ≤ (N : ℤ) := Int.natCast_nonneg N
    nlinarith [hM', hN', hM0, hN0]
