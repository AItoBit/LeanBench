by
  rintro ⟨x, y, h⟩
  -- the only zero of the form modulo `7` is the origin
  have key : ∀ a b : ZMod 7, a ^ 3 - 3 * a * b ^ 2 + b ^ 3 = 0 → a = 0 ∧ b = 0 := by
    decide
  have h2891 : (2891 : ZMod 7) = 0 := by decide
  have hc : ((x : ZMod 7)) ^ 3 - 3 * (x : ZMod 7) * ((y : ZMod 7)) ^ 2
      + ((y : ZMod 7)) ^ 3 = 0 := by
    have hh : ((x ^ 3 - 3 * x * y ^ 2 + y ^ 3 : ℤ) : ZMod 7) = ((2891 : ℤ) : ZMod 7) := by
      rw [h]
    push_cast at hh
    rw [hh, h2891]
  obtain ⟨hx0, hy0⟩ := key _ _ hc
  have hx : (7 : ℤ) ∣ x := by
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd x 7).mp hx0
    exact_mod_cast hd
  have hy : (7 : ℤ) ∣ y := by
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd y 7).mp hy0
    exact_mod_cast hd
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  obtain ⟨K, hK⟩ : ∃ K : ℤ, a ^ 3 - 3 * a * b ^ 2 + b ^ 3 = K := ⟨_, rfl⟩
  have h2 : 343 * K = 2891 := by rw [← hK]; linear_combination h
  omega
