by
  set Y : ℂ := (b - p) * (c - a) with hY
  set T : ℂ := (c - p) * (a - b) with hTdef
  set X : ℂ := (a - p) * (b - c) with hXdef
  have hsum : X + Y + T = 0 := by rw [hXdef, hY, hTdef]; exact sum_eq_zero a b c p
  have hXeq : X = -(Y + T) := by linear_combination hsum
  have hYT : Y + T ≠ 0 := fun h0 => hX (by rw [hXeq, h0, neg_zero])
  set s : ℂ := Y / T with hs
  have hYs : Y = s * T := by rw [hs]; field_simp
  have hs1 : s + 1 ≠ 0 := by
    intro h0
    apply hYT
    have hstep : Y + T = (s + 1) * T := by rw [hYs]; ring
    rw [h0, zero_mul] at hstep
    exact hstep
  have hA : X ^ 2 ≠ 0 := pow_ne_zero 2 hX
  have hB : (s + 1) ^ 2 ≠ 0 := pow_ne_zero 2 hs1
  have hrw : Y * T / X ^ 2 = s / (s + 1) ^ 2 := by
    rw [div_eq_div_iff hA hB, hXeq, hYs]
    ring
  rw [hrw] at hcond
  have habs : ‖s‖ = 1 := abs_ratio_eq_one hs1 hnr hcond
  have hT0 : ‖T‖ ≠ 0 := norm_ne_zero_iff.2 hT
  have hYn : ‖Y‖ = ‖T‖ := by
    have h1 : ‖Y‖ / ‖T‖ = 1 := by rw [← norm_div]; exact habs
    field_simp at h1
    exact h1
  rw [hY, hTdef] at hYn
  simpa [norm_mul] using hYn
