by
  constructor
  · -- `a = 481·76`, `b = 481·49`, `m = 962`, `n = 481`
    refine ⟨36556, 23569, 962, 481, by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num, by norm_num, by norm_num⟩
  · rintro k ⟨a, b, m, n, ha, hb, hm, hn, h1, h2, rfl⟩
    -- the key identity, over `ℤ`
    have h1' : (15 : ℤ) * a + 16 * b = (m : ℤ) ^ 2 := by exact_mod_cast h1
    have h2' : (16 : ℤ) * a = 15 * b + (n : ℤ) ^ 2 := by exact_mod_cast h2
    have key : (m : ℤ) ^ 4 + (n : ℤ) ^ 4 = 481 * ((a : ℤ) ^ 2 + (b : ℤ) ^ 2) := by
      linear_combination (-((m : ℤ) ^ 2 + 15 * a + 16 * b)) * h1'
        + (-((n : ℤ) ^ 2 + 16 * a - 15 * b)) * h2'
    -- divisibility by 13
    have h13 : (13 : ℕ) ∣ m ∧ (13 : ℕ) ∣ n := by
      have hz : ((m : ZMod 13)) ^ 4 + ((n : ZMod 13)) ^ 4 = 0 := by
        calc ((m : ZMod 13)) ^ 4 + ((n : ZMod 13)) ^ 4
            = ((((m : ℤ) ^ 4 + (n : ℤ) ^ 4 : ℤ)) : ZMod 13) := by push_cast; ring
          _ = (((481 * ((a : ℤ) ^ 2 + (b : ℤ) ^ 2) : ℤ)) : ZMod 13) := by rw [key]
          _ = 0 := by
              push_cast
              rw [show ((481 : ZMod 13)) = 0 by decide]
              ring
      obtain ⟨hx, hy⟩ := zmod13 _ _ hz
      exact ⟨(ZMod.natCast_eq_zero_iff m 13).1 hx,
        (ZMod.natCast_eq_zero_iff n 13).1 hy⟩
    -- divisibility by 37
    have h37 : (37 : ℕ) ∣ m ∧ (37 : ℕ) ∣ n := by
      have hz : ((m : ZMod 37)) ^ 4 + ((n : ZMod 37)) ^ 4 = 0 := by
        calc ((m : ZMod 37)) ^ 4 + ((n : ZMod 37)) ^ 4
            = ((((m : ℤ) ^ 4 + (n : ℤ) ^ 4 : ℤ)) : ZMod 37) := by push_cast; ring
          _ = (((481 * ((a : ℤ) ^ 2 + (b : ℤ) ^ 2) : ℤ)) : ZMod 37) := by rw [key]
          _ = 0 := by
              push_cast
              rw [show ((481 : ZMod 37)) = 0 by decide]
              ring
      obtain ⟨hx, hy⟩ := zmod37 _ _ hz
      exact ⟨(ZMod.natCast_eq_zero_iff m 37).1 hx,
        (ZMod.natCast_eq_zero_iff n 37).1 hy⟩
    -- hence `481 ∣ m` and `481 ∣ n`
    have hcop : Nat.Coprime 13 37 := by decide
    have hm481 : (481 : ℕ) ∣ m := by
      have h := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h13.1 h37.1
      norm_num at h
      exact h
    have hn481 : (481 : ℕ) ∣ n := by
      have h := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h13.2 h37.2
      norm_num at h
      exact h
    have hmge : 481 ≤ m := Nat.le_of_dvd hm hm481
    have hnge : 481 ≤ n := Nat.le_of_dvd hn hn481
    refine le_min ?_ ?_
    · calc (231361 : ℕ) = 481 ^ 2 := by norm_num
        _ ≤ m ^ 2 := Nat.pow_le_pow_left hmge 2
    · calc (231361 : ℕ) = 481 ^ 2 := by norm_num
        _ ≤ n ^ 2 := Nat.pow_le_pow_left hnge 2
