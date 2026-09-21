by
  refine ⟨imo1979P3Point O₁ O₂ A, fun t => ?_⟩
  set P : ℂ := imo1979P3Point O₁ O₂ A with hPdef
  set d : ℂ := O₂ - O₁ with hddef
  have hd : d ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have hdc : (starRingEnd ℂ) d ≠ 0 := by
    simpa using hd
  set N : ℂ := ((Complex.normSq (A - O₂) - Complex.normSq (A - O₁) : ℝ) : ℂ) with hNdef
  -- the two defining properties of `P`
  have hx : (P - A) * (starRingEnd ℂ) d = N := by
    have : P - A = N / (starRingEnd ℂ) d := by
      rw [hPdef, imo1979P3Point, hNdef, hddef]; ring
    rw [this, div_mul_cancel₀ _ hdc]
  have hNconj : (starRingEnd ℂ) N = N := by
    rw [hNdef]; exact Complex.conj_ofReal _
  have hy : (starRingEnd ℂ) (P - A) * d = N := by
    have := congrArg (starRingEnd ℂ) hx
    simpa [map_mul, hNconj, mul_comm] using this
  have hN : N = (A - O₂) * (starRingEnd ℂ) (A - O₂) - (A - O₁) * (starRingEnd ℂ) (A - O₁) := by
    rw [Complex.mul_conj, Complex.mul_conj, hNdef]; push_cast; ring
  -- reduce to an identity between squared distances
  set u : ℂ := Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I) with hudef
  have hu : u * (starRingEnd ℂ) u = 1 := by
    rw [Complex.mul_conj]
    have : ‖u‖ = 1 := by rw [hudef]; exact Complex.norm_exp_ofReal_mul_I _
    have h2 : ‖u‖ ^ 2 = Complex.normSq u := Complex.sq_norm u
    rw [this] at h2
    simp [← h2]
  have hB : imo1979P3Motion O₁ A t - P = (A - O₁) * (u - 1) - (P - A) := by
    rw [imo1979P3Motion, ← hudef]; ring
  have hC : imo1979P3Motion O₂ A t - P = (A - O₂) * (u - 1) - (P - A) := by
    rw [imo1979P3Motion, ← hudef]; ring
  have main : (imo1979P3Motion O₁ A t - P) * (starRingEnd ℂ) (imo1979P3Motion O₁ A t - P)
      = (imo1979P3Motion O₂ A t - P) * (starRingEnd ℂ) (imo1979P3Motion O₂ A t - P) := by
    rw [hB, hC]
    have e1 : (starRingEnd ℂ) ((A - O₁) * (u - 1) - (P - A))
        = (starRingEnd ℂ) (A - O₁) * ((starRingEnd ℂ) u - 1) - (starRingEnd ℂ) (P - A) := by
      simp [map_sub, map_mul]
    have e2 : (starRingEnd ℂ) ((A - O₂) * (u - 1) - (P - A))
        = (starRingEnd ℂ) (A - O₂) * ((starRingEnd ℂ) u - 1) - (starRingEnd ℂ) (P - A) := by
      simp [map_sub, map_mul]
    rw [e1, e2]
    refine key_identity (A - O₁) ((starRingEnd ℂ) (A - O₁)) (A - O₂) ((starRingEnd ℂ) (A - O₂))
      (P - A) ((starRingEnd ℂ) (P - A)) u ((starRingEnd ℂ) u) N hu ?_ ?_ hN
    · have : (starRingEnd ℂ) (A - O₁) - (starRingEnd ℂ) (A - O₂) = (starRingEnd ℂ) d := by
        rw [hddef, ← map_sub]; ring_nf
      rw [this]; exact hx
    · have : (A - O₁) - (A - O₂) = d := by rw [hddef]; ring
      rw [this]; exact hy
  rw [Complex.mul_conj, Complex.mul_conj] at main
  have hsq : Complex.normSq (imo1979P3Motion O₁ A t - P)
      = Complex.normSq (imo1979P3Motion O₂ A t - P) := by exact_mod_cast main
  rw [Complex.dist_eq, Complex.dist_eq, ← Real.sqrt_sq (norm_nonneg _),
    ← Real.sqrt_sq (norm_nonneg (imo1979P3Motion O₂ A t - P)), Complex.sq_norm, Complex.sq_norm,
    hsq]
