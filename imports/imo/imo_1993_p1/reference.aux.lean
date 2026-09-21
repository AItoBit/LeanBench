theorem f_monic (m : ℕ) : (f m).Monic := by
  unfold f
  monicity!

theorem f_natDegree (m : ℕ) : (f m).natDegree = m + 2 := by
  unfold f
  compute_degree!

theorem f_ne_zero (m : ℕ) : f m ≠ 0 := (f_monic m).ne_zero

theorem f_coeff_zero (m : ℕ) : (f m).coeff 0 = 3 := by
  unfold f
  simp

theorem f_eval (m : ℕ) (r : ℤ) : (f m).eval r = r ^ (m + 2) + 5 * r ^ (m + 1) + 3 := by
  unfold f
  simp

/-- The reduction of `f` modulo `3`. -/
theorem f_map3 (m : ℕ) :
    (f m).map (Int.castRingHom (ZMod 3)) = X ^ (m + 1) * (X + C 2) := by
  have h5 : (Int.castRingHom (ZMod 3)) (5 : ℤ) = 2 := by rw [eq_intCast]; decide
  have h3 : (Int.castRingHom (ZMod 3)) (3 : ℤ) = 0 := by rw [eq_intCast]; decide
  unfold f
  rw [Polynomial.map_add, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, Polynomial.map_C, h5, h3,
    Polynomial.C_0, add_zero]
  ring

/-- `f` has no integer root. -/
theorem f_no_root (m : ℕ) (r : ℤ) : (f m).eval r ≠ 0 := by
  rw [f_eval]
  intro hr
  have h2 : ((r : ZMod 2)) ^ (m + 2) + 5 * (r : ZMod 2) ^ (m + 1) + 3 = 0 := by
    have := congrArg (fun z : ℤ => (z : ZMod 2)) hr
    push_cast at this
    exact this
  have hcases : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  rcases hcases ((r : ZMod 2)) with hc | hc <;> rw [hc] at h2 <;> simp at h2 <;>
    revert h2 <;> decide

/-- If `3` does not divide the constant term of `h`, then `h` has degree at most one. -/
theorem natDegree_le_one_of_not_dvd (m : ℕ) (g h : ℤ[X]) (hgh : g * h = f m)
    (hc : ¬ ((3 : ℤ) ∣ h.coeff 0)) : h.natDegree ≤ 1 := by
  set φ := Int.castRingHom (ZMod 3) with hφ
  set G := g.map φ with hG
  set H := h.map φ with hH
  have hprod : G * H = X ^ (m + 1) * (X + C 2) := by
    rw [hG, hH, ← Polynomial.map_mul, hgh, f_map3]
  have hH0 : H.coeff 0 ≠ 0 := by
    rw [hH, Polynomial.coeff_map, hφ]
    simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hc
  have hXH : ¬ (X : (ZMod 3)[X]) ∣ H := by
    rw [Polynomial.X_dvd_iff]
    exact hH0
  have hdvd : (X : (ZMod 3)[X]) ^ (m + 1) ∣ G * H := by
    rw [hprod]
    exact Dvd.intro _ rfl
  have hGdvd : (X : (ZMod 3)[X]) ^ (m + 1) ∣ G :=
    Polynomial.prime_X.pow_dvd_of_dvd_mul_right (m + 1) hXH hdvd
  have hne : G * H ≠ 0 := by
    rw [hprod]
    exact mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (Polynomial.X_add_C_ne_zero _)
  have hG0 : G ≠ 0 := fun h0 => hne (by rw [h0, zero_mul])
  have hH0' : H ≠ 0 := fun h0 => hne (by rw [h0, mul_zero])
  have hGdeg : m + 1 ≤ G.natDegree := by
    have hd := Polynomial.natDegree_le_of_dvd hGdvd hG0
    simpa using hd
  have hsum : G.natDegree + H.natDegree = m + 2 := by
    rw [← Polynomial.natDegree_mul hG0 hH0', hprod,
      Polynomial.natDegree_mul (pow_ne_zero _ Polynomial.X_ne_zero)
        (Polynomial.X_add_C_ne_zero _),
      Polynomial.natDegree_X_pow, Polynomial.natDegree_X_add_C]
  have hlead : g.leadingCoeff * h.leadingCoeff = 1 := by
    have hl := congrArg Polynomial.leadingCoeff hgh
    rwa [Polynomial.leadingCoeff_mul, (f_monic m).leadingCoeff] at hl
  have hdvd1 : h.leadingCoeff ∣ 1 := ⟨g.leadingCoeff, by rw [← hlead]; ring⟩
  have hu : IsUnit h.leadingCoeff := isUnit_of_dvd_one hdvd1
  have hnz : φ h.leadingCoeff ≠ 0 := by
    rcases Int.isUnit_iff.1 hu with h1 | h1 <;> rw [h1, hφ, eq_intCast] <;> decide
  have hkeep : H.natDegree = h.natDegree := by
    rw [hH]
    exact Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hnz
  omega
