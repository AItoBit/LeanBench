by
  constructor
  · intro hd
    have haZ : (0 : ℤ) < a := by
      exact_mod_cast ha
    have hbZ : (0 : ℤ) < b := by
      exact_mod_cast hb
    have hdZ :
        (a : ℤ) * (b : ℤ) ^ 2 + b + 7 ∣
          (a : ℤ) ^ 2 * b + a + b := by
      exact_mod_cast hd

    rcases classify_int a b haZ hbZ hdZ with
      he | ⟨hb1, ha1 | ha2⟩

    · have heN : 7 * a = b ^ 2 := by
        exact_mod_cast he
      have hp : Nat.Prime 7 := by decide
      have hd7 : 7 ∣ b :=
        hp.dvd_of_dvd_pow (by
          rw [← heN]
          exact dvd_mul_right 7 a)
      obtain ⟨t, ht⟩ := hd7
      have htpos : 0 < t := by omega
      have haeq : a = 7 * t ^ 2 := by
        nlinarith [heN]
      exact Or.inr (Or.inr ⟨t, htpos, haeq, ht⟩)

    · left
      exact ⟨by exact_mod_cast ha1, by exact_mod_cast hb1⟩

    · right
      left
      exact ⟨by exact_mod_cast ha2, by exact_mod_cast hb1⟩

  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨t, ht, rfl, rfl⟩)
    · norm_num
    · norm_num
    · exact ⟨t, by ring⟩
