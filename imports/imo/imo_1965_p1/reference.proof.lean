by
  constructor
  · rintro ⟨hl, -⟩
    rw [abs_sqrt_sub_sqrt_eq] at hl
    have hc : Real.cos x ≤ |Real.sin x| :=
      (le_min_iff.mp (by linarith : Real.cos x ≤ min |Real.sin x| |Real.cos x|)).1
    exact (cos_le_abs_sin_iff h0 h2).mp hc
  · rintro ⟨hx1, hx2⟩
    refine ⟨?_, abs_sqrt_sub_sqrt_le_sqrt_two x⟩
    rw [abs_sqrt_sub_sqrt_eq]
    have hc : Real.cos x ≤ |Real.sin x| := (cos_le_abs_sin_iff h0 h2).mpr ⟨hx1, hx2⟩
    have : Real.cos x ≤ min |Real.sin x| |Real.cos x| := le_min hc (le_abs_self _)
    linarith
