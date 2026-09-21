by
  have ha' : (0 : ℤ) < a := by exact_mod_cast ha
  have hb' : (0 : ℤ) < b := by exact_mod_cast hb
  have hc' : (0 : ℤ) < c := by exact_mod_cast hc
  constructor
  · -- `2abc - ab - bc - ca` is not representable
    rintro ⟨x, y, z, hxyz⟩
    -- `a ∣ x + 1`
    have hxa : (a : ℤ) ≤ (x : ℤ) + 1 := by
      have hdvd : (a : ℤ) ∣ ((x : ℤ) + 1) * ((b : ℤ) * c) := by
        refine ⟨2 * b * c - b - c - y * c - z * b, ?_⟩
        linarith [hxyz, (by ring : ((x : ℤ) + 1) * ((b : ℤ) * c)
          = (x : ℤ) * (b * c) + b * c)]
      have hcop : IsCoprime (a : ℤ) ((b : ℤ) * c) := by
        have : Nat.Coprime a (b * c) := Nat.Coprime.mul_right hab hca.symm
        exact_mod_cast Nat.isCoprime_iff_coprime.mpr this
      have := hcop.dvd_of_dvd_mul_right hdvd
      exact Int.le_of_dvd (by positivity) this
    have hyb : (b : ℤ) ≤ (y : ℤ) + 1 := by
      have hdvd : (b : ℤ) ∣ ((y : ℤ) + 1) * ((c : ℤ) * a) := by
        refine ⟨2 * a * c - a - c - x * c - z * a, ?_⟩
        linarith [hxyz, (by ring : ((y : ℤ) + 1) * ((c : ℤ) * a)
          = (y : ℤ) * (c * a) + c * a)]
      have hcop : IsCoprime (b : ℤ) ((c : ℤ) * a) := by
        have : Nat.Coprime b (c * a) := Nat.Coprime.mul_right hbc hab.symm
        exact_mod_cast Nat.isCoprime_iff_coprime.mpr this
      have := hcop.dvd_of_dvd_mul_right hdvd
      exact Int.le_of_dvd (by positivity) this
    have hzc : (c : ℤ) ≤ (z : ℤ) + 1 := by
      have hdvd : (c : ℤ) ∣ ((z : ℤ) + 1) * ((a : ℤ) * b) := by
        refine ⟨2 * a * b - a - b - x * b - y * a, ?_⟩
        linarith [hxyz, (by ring : ((z : ℤ) + 1) * ((a : ℤ) * b)
          = (z : ℤ) * (a * b) + a * b)]
      have hcop : IsCoprime (c : ℤ) ((a : ℤ) * b) := by
        have : Nat.Coprime c (a * b) := Nat.Coprime.mul_right hca hbc.symm
        exact_mod_cast Nat.isCoprime_iff_coprime.mpr this
      have := hcop.dvd_of_dvd_mul_right hdvd
      exact Int.le_of_dvd (by positivity) this
    nlinarith [hxyz, hxa, hyb, hzc, mul_pos (mul_pos ha' hb') hc',
      mul_pos hb' hc', mul_pos hc' ha', mul_pos ha' hb']
  · -- every larger integer is representable
    rintro n hn
    by_contra hlt
    push_neg at hlt
    apply hn
    -- choose `x < a` with `a ∣ n - x * (b*c)`
    have hcop : IsCoprime ((b : ℤ) * c) (a : ℤ) := by
      have : Nat.Coprime (b * c) a := Nat.Coprime.mul_left (hab.symm) hca
      exact_mod_cast Nat.isCoprime_iff_coprime.mpr this
    obtain ⟨x, hxlt, hdvd⟩ := exists_small_nat_smul_congr ha' hcop n
    obtain ⟨m, hm⟩ := hdvd
    have hxle : (x : ℤ) ≤ (a : ℤ) - 1 := by omega
    have hmge : ((b : ℤ) - 1) * ((c : ℤ) - 1) ≤ m := by
      have key : (a : ℤ) * (((b : ℤ) - 1) * ((c : ℤ) - 1) - 1) < a * m := by
        nlinarith [hm, hxle, hlt, mul_pos hb' hc']
      have := lt_of_mul_lt_mul_left key ha'.le
      linarith
    obtain ⟨y, z, hyz⟩ := exists_repr_of_ge hb hbc m hmge
    exact ⟨x, y, z, by rw [hyz] at hm; linarith [hm]⟩
