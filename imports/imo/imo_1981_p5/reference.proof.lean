by
  -- notation for the side lengths, twice the area, and the perimeter
  set na := ‖C - B‖ with hna
  set nb := ‖C - A‖ with hnb
  set nc := ‖B - A‖ with hnc
  set D := Real.sqrt (gram A B C) with hD
  have hDpos : 0 < D := Real.sqrt_pos.2 (gram_pos A B C hABC)
  have hAB : B - A ≠ 0 := by
    intro h
    refine hABC ?_
    have hBA : B = A := by rw [← sub_eq_zero]; exact h
    subst hBA
    exact (collinear_pair ℝ B C).subset (by intro x hx; simp at hx ⊢; tauto)
  have hncpos : 0 < nc := by rw [hnc, norm_pos_iff]; exact hAB
  have hsp : 0 < na + nb + nc := by
    have h1 : 0 ≤ na := norm_nonneg _
    have h2 : 0 ≤ nb := norm_nonneg _
    linarith
  -- barycentric coordinates of the three centres
  obtain ⟨a1, b1, c1, ha1, hb1, hc1, hs1, hOA⟩ := exists_barycentric A B C OA hOAmem
  obtain ⟨a2, b2, c2, ha2, hb2, hc2, hs2, hOB⟩ := exists_barycentric A B C OB hOBmem
  obtain ⟨a3, b3, c3, ha3, hb3, hc3, hs3, hOC⟩ := exists_barycentric A B C OC hOCmem
  have e1 : r * nc = c1 * D := coeff_AB A B C OA a1 b1 c1 r hs1 hc1 hOA hOA1
  have e2 : r * nb = b1 * D := coeff_AC A B C OA a1 b1 c1 r hs1 hb1 hOA hOA2
  have e3 : r * nc = c2 * D := coeff_AB A B C OB a2 b2 c2 r hs2 hc2 hOB hOB1
  have e4 : r * na = a2 * D := coeff_BC A B C OB a2 b2 c2 r hs2 ha2 hOB hOB2
  have e5 : r * nb = b3 * D := coeff_AC A B C OC a3 b3 c3 r hs3 hb3 hOC hOC1
  have e6 : r * na = a3 * D := coeff_BC A B C OC a3 b3 c3 r hs3 ha3 hOC hOC2
  have hDne : D ≠ 0 := ne_of_gt hDpos
  have hsne : na + nb + nc ≠ 0 := ne_of_gt hsp
  -- the common ratio of the homothety
  set t : ℝ := r * (na + nb + nc) / D with ht
  -- the incenter, written in barycentric coordinates
  set I : Pt := (na / (na + nb + nc)) • A + (nb / (na + nb + nc)) • B +
    (nc / (na + nb + nc)) • C with hI
  have hIeq : incenter A B C = I := by
    rw [hI, incenter, dist_eq_norm, dist_eq_norm, dist_eq_norm, norm_sub_rev B C,
      norm_sub_rev A B, ← hna, ← hnb, ← hnc]
  -- the homothety with centre `I` and ratio `1 - t` maps the vertices to the centres
  have hOAeq : OA = (1 - t) • A + t • I := by
    rw [hOA, hI, ht]
    have hb1' : b1 = r * nb / D := by field_simp; linarith
    have hc1' : c1 = r * nc / D := by field_simp; linarith
    have ha1' : a1 = 1 - r * nb / D - r * nc / D := by rw [← hb1', ← hc1']; linarith
    rw [ha1', hb1', hc1']
    match_scalars <;> (field_simp; try ring)
  have hOBeq : OB = (1 - t) • B + t • I := by
    rw [hOB, hI, ht]
    have ha2' : a2 = r * na / D := by field_simp; linarith
    have hc2' : c2 = r * nc / D := by field_simp; linarith
    have hb2' : b2 = 1 - r * na / D - r * nc / D := by rw [← ha2', ← hc2']; linarith
    rw [ha2', hb2', hc2']
    match_scalars <;> (field_simp; try ring)
  have hOCeq : OC = (1 - t) • C + t • I := by
    rw [hOC, hI, ht]
    have ha3' : a3 = r * na / D := by field_simp; linarith
    have hb3' : b3 = r * nb / D := by field_simp; linarith
    have hc3' : c3 = 1 - r * na / D - r * nb / D := by rw [← ha3', ← hb3']; linarith
    rw [ha3', hb3', hc3']
    match_scalars <;> (field_simp; try ring)
  -- the homothety is nondegenerate
  have h1t : (1 : ℝ) - t ≠ 0 := by
    intro h
    exact hne (by rw [hOAeq, hOBeq, h]; module)
  -- the image of the circumcenter under the homothety
  set Y : Pt := (1 - t) • X + t • I with hY
  have hYA : Y - OA = (1 - t) • (X - A) := by rw [hY, hOAeq]; module
  have hYB : Y - OB = (1 - t) • (X - B) := by rw [hY, hOBeq]; module
  have hYC : Y - OC = (1 - t) • (X - C) := by rw [hY, hOCeq]; module
  have hnXB : ‖X - A‖ = ‖X - B‖ := by rw [← dist_eq_norm, ← dist_eq_norm]; exact hXB
  have hnXC : ‖X - A‖ = ‖X - C‖ := by rw [← dist_eq_norm, ← dist_eq_norm]; exact hXC
  have hYAB : dist Y OA = dist Y OB := by
    rw [dist_eq_norm, dist_eq_norm, hYA, hYB, norm_smul, norm_smul, hnXB]
  have hYAC : dist Y OA = dist Y OC := by
    rw [dist_eq_norm, dist_eq_norm, hYA, hYC, norm_smul, norm_smul, hnXC]
  -- `O` and `Y` are both equidistant from the three centres, hence equal
  have hOAB : dist O OA = dist O OB := by rw [hOOA, hOOB]
  have hOAC : dist O OA = dist O OC := by rw [hOOA, hOOC]
  have hp1 : ⟪O - Y, OB - OA⟫ = 0 := inner_eq_zero_of_dist_eq OA OB O Y hOAB hYAB
  have hp2 : ⟪O - Y, OC - OA⟫ = 0 := inner_eq_zero_of_dist_eq OA OC O Y hOAC hYAC
  have hdiff1 : OB - OA = (1 - t) • (B - A) := by rw [hOAeq, hOBeq]; module
  have hdiff2 : OC - OA = (1 - t) • (C - A) := by rw [hOAeq, hOCeq]; module
  rw [hdiff1, real_inner_smul_right] at hp1
  rw [hdiff2, real_inner_smul_right] at hp2
  have hq1 : ⟪O - Y, B - A⟫ = 0 := by
    rcases mul_eq_zero.1 hp1 with h | h
    · exact absurd h h1t
    · exact h
  have hq2 : ⟪O - Y, C - A⟫ = 0 := by
    rcases mul_eq_zero.1 hp2 with h | h
    · exact absurd h h1t
    · exact h
  have hOY : O = Y := by
    have := eq_zero_of_orthogonal_two (O - Y) (B - A) (C - A) hq1 hq2
      (by rw [← hnb, ← hnc]; exact gram_pos A B C hABC)
    rwa [sub_eq_zero] at this
  -- conclude
  rw [hIeq, collinear_iff_of_mem (Set.mem_insert I {X, O})]
  refine ⟨X - I, ?_⟩
  rintro p (rfl | rfl | rfl)
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩
  · exact ⟨1 - t, by rw [hOY, hY]; simp only [vadd_eq_add]; module⟩

/-! ### The hypotheses are not vacuous

We exhibit an explicit configuration satisfying all the hypotheses of `candidate`: the
`3`-`4`-`5` right triangle with vertices `(0,0)`, `(4,0)`, `(0,3)`, three circles of radius
`5/7` centred at `(5/7, 5/7)`, `(13/7, 5/7)` and `(5/7, 11/7)`, all passing through the
common point `(9/7, 8/7)`, and the circumcenter `(2, 3/2)`.
-/
