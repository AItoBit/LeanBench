by
  have hOG : O = (4 : ℝ)⁻¹ • (A + B + C + D) :=
    circumcenter_eq_centroid A B C D O s hs hAB hAC hAD hBC hBD hCD hOA hOB hOC
  set G : E := (4 : ℝ)⁻¹ • (A + B + C + D) with hG
  set a := A - G with hadef
  set b := B - G with hbdef
  set c := C - G with hcdef
  set d := D - G with hddef
  have hsum : a + b + c + d = 0 := by
    rw [hadef, hbdef, hcdef, hddef, hG]; module
  have dab : ‖a - b‖ = s := by rw [hadef, hbdef]; simpa [dist_eq_norm, sub_sub_sub_cancel_right]
    using hAB
  have dac : ‖a - c‖ = s := by rw [hadef, hcdef]; simpa [dist_eq_norm, sub_sub_sub_cancel_right]
    using hAC
  have dad : ‖a - d‖ = s := by rw [hadef, hddef]; simpa [dist_eq_norm, sub_sub_sub_cancel_right]
    using hAD
  have dbc : ‖b - c‖ = s := by rw [hbdef, hcdef]; simpa [dist_eq_norm, sub_sub_sub_cancel_right]
    using hBC
  have dbd : ‖b - d‖ = s := by rw [hbdef, hddef]; simpa [dist_eq_norm, sub_sub_sub_cancel_right]
    using hBD
  have dcd : ‖c - d‖ = s := by rw [hcdef, hddef]; simpa [dist_eq_norm, sub_sub_sub_cancel_right]
    using hCD
  obtain ⟨na, nb, nc, nd, iab, -, -, -, -, -⟩ :=
    tetra_facts a b c d s hsum dab dac dad dbc dbd dcd
  -- the circumradius
  set R : ℝ := Real.sqrt (3 * s ^ 2 / 8) with hRdef
  have hRpos : 0 < R := Real.sqrt_pos.mpr (by positivity)
  have hRsq : R ^ 2 = 3 * s ^ 2 / 8 := Real.sq_sqrt (by positivity)
  have hnorm : ∀ x : E, ‖x‖ ^ 2 = 3 * s ^ 2 / 8 → ‖x‖ = R := by
    intro x hx
    have : ‖x‖ ^ 2 = R ^ 2 := by rw [hx, hRsq]
    nlinarith [norm_nonneg x, hRpos]
  have ha := hnorm a na
  have hb := hnorm b nb
  have hc := hnorm c nc
  have hd := hnorm d nd
  have hab : ⟪a, b⟫ = -R ^ 2 / 3 := by rw [iab, hRsq]; ring
  set p := P - G with hpdef
  have hp : p ≠ 0 := by
    rw [hpdef, sub_ne_zero]
    exact fun h => hPO (h.trans hOG.symm)
  have hPA : dist P A = ‖a - p‖ := by
    rw [hadef, hpdef, dist_eq_norm, sub_sub_sub_cancel_right, norm_sub_rev]
  have hPB : dist P B = ‖b - p‖ := by
    rw [hbdef, hpdef, dist_eq_norm, sub_sub_sub_cancel_right, norm_sub_rev]
  have hPC : dist P C = ‖c - p‖ := by
    rw [hcdef, hpdef, dist_eq_norm, sub_sub_sub_cancel_right, norm_sub_rev]
  have hPD : dist P D = ‖d - p‖ := by
    rw [hddef, hpdef, dist_eq_norm, sub_sub_sub_cancel_right, norm_sub_rev]
  have hOAv : dist O A = R := by
    rw [hOG, dist_eq_norm, norm_sub_rev]; exact ha
  have hOBv : dist O B = R := by
    rw [hOG, dist_eq_norm, norm_sub_rev]; exact hb
  have hOCv : dist O C = R := by
    rw [hOG, dist_eq_norm, norm_sub_rev]; exact hc
  have hODv : dist O D = R := by
    rw [hOG, dist_eq_norm, norm_sub_rev]; exact hd
  rw [hOAv, hOBv, hOCv, hODv, hPA, hPB, hPC, hPD]
  have := sum_dist_gt a b c d p R hRpos hsum ha hb hc hd hab hp
  linarith
