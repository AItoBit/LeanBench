by
  set A : ℕ := digitSum (4444 ^ 4444) with hA
  set B : ℕ := digitSum A with hB
  -- `A ≤ 9 * 17776 = 159984 < 10 ^ 6`
  have hA6 : A < 10 ^ 6 := lt_of_le_of_lt (digitSum_le_of_lt_pow pow_lt) (by norm_num)
  -- hence `B ≤ 54`
  have hB54 : B ≤ 54 := by
    have := digitSum_le_of_lt_pow (n := A) (k := 6) hA6
    omega
  -- and `B ≡ 4444 ^ 4444 ≡ 7 [MOD 9]`
  have hBmod : B % 9 = 7 := by
    rw [hB, digitSum_mod_nine, hA, digitSum_mod_nine, pow_mod_nine]
  exact digitSum_eq_seven_of_le_54 B hB54 hBmod
