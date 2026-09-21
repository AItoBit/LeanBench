by
  obtain ⟨ν, hνdef⟩ : ∃ r : ℝ, r = ‖n‖ := ⟨_, rfl⟩
  have hν : 0 < ν := hνdef ▸ norm_pos_iff.mpr hn
  -- the unit normal
  obtain ⟨u, hudef⟩ : ∃ x : E3, x = ν⁻¹ • n := ⟨_, rfl⟩
  have hu : ‖u‖ = 1 := by
    rw [hudef, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hν), ← hνdef,
      inv_mul_cancel₀ hν.ne']
  have hnu : n = ν • u := by
    rw [hudef, smul_smul, mul_inv_cancel₀ hν.ne', one_smul]
  -- the levels, rescaled to the unit normal and centred at their mean
  obtain ⟨μ, hμdef⟩ : ∃ r : ℝ, r = (c 0 + c 1 + c 2 + c 3) / (4 * ν) := ⟨_, rfl⟩
  obtain ⟨d, hddef⟩ : ∃ f : Fin 4 → ℝ, f = fun i => c i / ν - μ := ⟨_, rfl⟩
  have hdsum : d 0 + d 1 + d 2 + d 3 = 0 := by
    rw [hddef, hμdef]; field_simp; ring
  have hdc : ∀ i, ν * (μ + d i) = c i := by
    intro i; rw [hddef]; field_simp; ring
  -- the direction realising the prescribed projections
  obtain ⟨w, hwdef⟩ : ∃ x : E3, x = (!₂[(d 0 + d 1) / 2, (d 0 + d 2) / 2, (d 0 + d 3) / 2] : E3) :=
    ⟨_, rfl⟩
  have key : ∀ i, ⟪T i, w⟫_ℝ = d i := by
    intro i; rw [hwdef]; exact inner_T_w d hdsum i
  have hw : w ≠ 0 := by
    intro h
    have hd : ∀ i, d i = 0 := fun i => by rw [← key i, h, inner_zero_right]
    have h0 := hd 0
    have h1 := hd 1
    rw [hddef] at h0 h1
    simp only at h0 h1
    have : c 0 = c 1 := by
      have : c 0 / ν = c 1 / ν := by linarith
      field_simp at this
      exact this
    exact absurd (hc this) (by decide)
  obtain ⟨W, hWdef⟩ : ∃ r : ℝ, r = ‖w‖ := ⟨_, rfl⟩
  have hW : 0 < W := hWdef ▸ norm_pos_iff.mpr hw
  obtain ⟨v, hvdef⟩ : ∃ x : E3, x = W⁻¹ • w := ⟨_, rfl⟩
  have hv : ‖v‖ = 1 := by
    rw [hvdef, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hW), ← hWdef,
      inv_mul_cancel₀ hW.ne']
  obtain ⟨R, hR⟩ := exists_linearIsometryEquiv_map u v hu hv
  refine ⟨fun i => μ • u + W • R (T i), 2 * Real.sqrt 2 * W, by positivity, ?_, ?_⟩
  · intro i
    have huu : ⟪u, n⟫_ℝ = ν := by
      rw [hudef, real_inner_smul_left, real_inner_self_eq_norm_sq, ← hνdef]
      field_simp
    have hRi : ⟪R (T i), n⟫_ℝ = ν * (W⁻¹ * d i) := by
      rw [hnu, real_inner_smul_right, ← hR, LinearIsometryEquiv.inner_map_map, hvdef,
        real_inner_smul_right, key i]
    simp only
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, huu, hRi,
      show W * (ν * (W⁻¹ * d i)) = ν * d i by field_simp,
      show μ * ν + ν * d i = ν * (μ + d i) by ring, hdc i]
  · intro i j hij
    have hsub : (μ • u + W • R (T i)) - (μ • u + W • R (T j)) = W • R (T i - T j) := by
      rw [map_sub]; module
    simp only
    rw [dist_eq_norm, hsub, norm_smul, LinearIsometryEquiv.norm_map, norm_T_sub i j hij,
      Real.norm_eq_abs, abs_of_pos hW]
    ring
