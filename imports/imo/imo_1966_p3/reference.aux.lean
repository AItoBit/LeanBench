/-- Basic metric relations for the four vectors pointing from the centroid of a regular
tetrahedron (with edge length `s`) to its vertices: each has squared length `3 s ^ 2 / 8`,
and any two of them have inner product `-s ^ 2 / 8`. -/
lemma tetra_facts (a b c d : E) (s : ℝ)
    (hsum : a + b + c + d = 0)
    (hab : ‖a - b‖ = s) (hac : ‖a - c‖ = s) (had : ‖a - d‖ = s)
    (hbc : ‖b - c‖ = s) (hbd : ‖b - d‖ = s) (hcd : ‖c - d‖ = s) :
    ‖a‖ ^ 2 = 3 * s ^ 2 / 8 ∧ ‖b‖ ^ 2 = 3 * s ^ 2 / 8 ∧ ‖c‖ ^ 2 = 3 * s ^ 2 / 8 ∧
      ‖d‖ ^ 2 = 3 * s ^ 2 / 8 ∧ ⟪a, b⟫ = -s ^ 2 / 8 ∧ ⟪a, c⟫ = -s ^ 2 / 8 ∧
      ⟪a, d⟫ = -s ^ 2 / 8 ∧ ⟪b, c⟫ = -s ^ 2 / 8 ∧ ⟪b, d⟫ = -s ^ 2 / 8 ∧
      ⟪c, d⟫ = -s ^ 2 / 8 := by
  have hdd : d = -a - b - c := by linear_combination (norm := module) hsum
  subst hdd
  have key : ∀ x y : E, ‖x - y‖ = s → ⟪x - y, x - y⟫ = s ^ 2 := by
    intro x y h; rw [real_inner_self_eq_norm_sq, h]
  have e1 := key _ _ hab
  have e2 := key _ _ hac
  have e3 := key _ _ had
  have e4 := key _ _ hbc
  have e5 := key _ _ hbd
  have e6 := key _ _ hcd
  have e7 : ‖-a - b - c‖ ^ 2 = ⟪-a - b - c, -a - b - c⟫ := (real_inner_self_eq_norm_sq _).symm
  simp only [inner_sub_left, inner_sub_right, inner_neg_left, inner_neg_right,
    real_inner_self_eq_norm_sq] at e1 e2 e3 e4 e5 e6 e7 ⊢
  have cab := real_inner_comm a b
  have cac := real_inner_comm a c
  have cbc := real_inner_comm b c
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith⟩

/-- Strict form of the key estimate: if `a, b, c, d` are four vectors of common length `R > 0`
summing to zero, any two of which make the "tetrahedral" angle (inner product `-R ^ 2 / 3`),
then translating by a nonzero vector `p` strictly increases the sum of the distances to
`a, b, c, d`. -/
lemma sum_dist_gt (a b c d p : E) (R : ℝ) (hR : 0 < R)
    (hsum : a + b + c + d = 0)
    (ha : ‖a‖ = R) (hb : ‖b‖ = R) (hc : ‖c‖ = R) (hd : ‖d‖ = R)
    (hab : ⟪a, b⟫ = -R ^ 2 / 3) (hp : p ≠ 0) :
    4 * R < ‖a - p‖ + ‖b - p‖ + ‖c - p‖ + ‖d - p‖ := by
  have hba : ⟪b, a⟫ = -R ^ 2 / 3 := by rw [real_inner_comm]; exact hab
  have cs : ∀ x : E, ‖x‖ = R → ⟪x - p, x⟫ ≤ ‖x - p‖ * R := by
    intro x hx
    have h := real_inner_le_norm (x - p) x
    rwa [hx] at h
  -- Cauchy-Schwarz is strict for at least one of `a`, `b`.
  have key : ⟪a - p, a⟫ < ‖a - p‖ * R ∨ ⟪b - p, b⟫ < ‖b - p‖ * R := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2⟩ := hcon
    have ea : ⟪a - p, a⟫ = ‖a - p‖ * ‖a‖ := by rw [ha]; linarith [cs a ha]
    have eb : ⟪b - p, b⟫ = ‖b - p‖ * ‖b‖ := by rw [hb]; linarith [cs b hb]
    rw [inner_eq_norm_mul_iff_real, ha] at ea
    rw [inner_eq_norm_mul_iff_real, hb] at eb
    have ea' : R • p = (R - ‖a - p‖) • a := by
      rw [smul_sub, sub_smul] at *
      linear_combination (norm := module) -ea
    have eb' : R • p = (R - ‖b - p‖) • b := by
      rw [smul_sub, sub_smul] at *
      linear_combination (norm := module) -eb
    set mu := R - ‖a - p‖ with hmu
    set nu := R - ‖b - p‖ with hnu
    have hmn : mu • a = nu • b := by rw [← ea', ← eb']
    have i1 := congrArg (fun v => ⟪v, a⟫) hmn
    have i2 := congrArg (fun v => ⟪v, b⟫) hmn
    simp only [real_inner_smul_left, real_inner_self_eq_norm_sq, ha, hb, hba, hab] at i1 i2
    have hR2 : (0 : ℝ) < R ^ 2 := by positivity
    have hnu0 : nu = 0 := by nlinarith
    have hp0 : R • p = 0 := by rw [eb', hnu0, zero_smul]
    exact hp (by simpa [hR.ne'] using hp0)
  have hsum2 : ⟪a - p, a⟫ + ⟪b - p, b⟫ + ⟪c - p, c⟫ + ⟪d - p, d⟫ = 4 * R ^ 2 := by
    have hz : ⟪p, a⟫ + ⟪p, b⟫ + ⟪p, c⟫ + ⟪p, d⟫ = 0 := by
      have h0 : ⟪p, a + b + c + d⟫ = 0 := by rw [hsum, inner_zero_right]
      simpa [inner_add_right] using h0
    simp only [inner_sub_left, real_inner_self_eq_norm_sq, ha, hb, hc, hd]
    have c1 := real_inner_comm p a
    have c2 := real_inner_comm p b
    have c3 := real_inner_comm p c
    have c4 := real_inner_comm p d
    linarith
  have ha' := cs a ha
  have hb' := cs b hb
  have hc' := cs c hc
  have hd' := cs d hd
  have hlt : 4 * R ^ 2 < (‖a - p‖ + ‖b - p‖ + ‖c - p‖ + ‖d - p‖) * R := by
    rcases key with h | h <;> nlinarith
  nlinarith

/-- The three edge vectors of a regular tetrahedron issuing from the centroid towards three
of its vertices are linearly independent. -/
lemma tetra_span (a b c : E) (s : ℝ) (hs : 0 < s)
    (ha : ‖a‖ ^ 2 = 3 * s ^ 2 / 8) (hb : ‖b‖ ^ 2 = 3 * s ^ 2 / 8) (hc : ‖c‖ ^ 2 = 3 * s ^ 2 / 8)
    (hab : ⟪a, b⟫ = -s ^ 2 / 8) (hac : ⟪a, c⟫ = -s ^ 2 / 8) (hbc : ⟪b, c⟫ = -s ^ 2 / 8) :
    Submodule.span ℝ (Set.range ![a, b, c]) = ⊤ := by
  have hba : ⟪b, a⟫ = -s ^ 2 / 8 := by rw [real_inner_comm]; exact hab
  have hca : ⟪c, a⟫ = -s ^ 2 / 8 := by rw [real_inner_comm]; exact hac
  have hcb : ⟪c, b⟫ = -s ^ 2 / 8 := by rw [real_inner_comm]; exact hbc
  have hli : LinearIndependent ℝ ![a, b, c] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at hg
    have i1 := congrArg (fun v => ⟪v, a⟫) hg
    have i2 := congrArg (fun v => ⟪v, b⟫) hg
    have i3 := congrArg (fun v => ⟪v, c⟫) hg
    simp only [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      inner_zero_left, ha, hb, hc, hab, hac, hba, hbc, hca, hcb] at i1 i2 i3
    have hs2 : (0 : ℝ) < s ^ 2 := by positivity
    have h0 : g 0 = 0 := by nlinarith
    have h1 : g 1 = 0 := by nlinarith
    have h2 : g 2 = 0 := by nlinarith
    intro i
    fin_cases i <;> assumption
  refine hli.span_eq_top_of_card_eq_finrank ?_
  simp

/-- The center of the circumscribed sphere of a regular tetrahedron is its centroid. -/
theorem circumcenter_eq_centroid (A B C D O : E) (s : ℝ) (hs : 0 < s)
    (hAB : dist A B = s) (hAC : dist A C = s) (hAD : dist A D = s)
    (hBC : dist B C = s) (hBD : dist B D = s) (hCD : dist C D = s)
    (hOA : dist O A = dist O B) (hOB : dist O B = dist O C) (hOC : dist O C = dist O D) :
    O = (4 : ℝ)⁻¹ • (A + B + C + D) := by
  set G : E := (4 : ℝ)⁻¹ • (A + B + C + D) with hG
  set a := A - G with hadef
  set b := B - G with hbdef
  set c := C - G with hcdef
  set d := D - G with hddef
  have hsum : a + b + c + d = 0 := by
    rw [hadef, hbdef, hcdef, hddef, hG]
    module
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
  obtain ⟨na, nb, nc, nd, iab, iac, iad, ibc, ibd, icd⟩ :=
    tetra_facts a b c d s hsum dab dac dad dbc dbd dcd
  set u := O - G with hudef
  -- rewrite the equidistance hypotheses in terms of `u`
  have hda : dist O A = ‖a - u‖ := by
    rw [hadef, hudef, dist_eq_norm, sub_sub_sub_cancel_right, norm_sub_rev]
  have hdb : dist O B = ‖b - u‖ := by
    rw [hbdef, hudef, dist_eq_norm, sub_sub_sub_cancel_right, norm_sub_rev]
  have hdc : dist O C = ‖c - u‖ := by
    rw [hcdef, hudef, dist_eq_norm, sub_sub_sub_cancel_right, norm_sub_rev]
  have hdd : dist O D = ‖d - u‖ := by
    rw [hddef, hudef, dist_eq_norm, sub_sub_sub_cancel_right, norm_sub_rev]
  have expand : ∀ x : E, ‖x - u‖ ^ 2 = ‖x‖ ^ 2 - 2 * ⟪x, u⟫ + ‖u‖ ^ 2 := by
    intro x
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq]
    have := real_inner_comm u x
    linarith
  have eqab : ⟪a, u⟫ = ⟪b, u⟫ := by
    have h : ‖a - u‖ ^ 2 = ‖b - u‖ ^ 2 := by rw [← hda, ← hdb, hOA]
    rw [expand, expand] at h; linarith
  have eqbc : ⟪b, u⟫ = ⟪c, u⟫ := by
    have h : ‖b - u‖ ^ 2 = ‖c - u‖ ^ 2 := by rw [← hdb, ← hdc, hOB]
    rw [expand, expand] at h; linarith
  have eqcd : ⟪c, u⟫ = ⟪d, u⟫ := by
    have h : ‖c - u‖ ^ 2 = ‖d - u‖ ^ 2 := by rw [← hdc, ← hdd, hOC]
    rw [expand, expand] at h; linarith
  have hz : ⟪a, u⟫ + ⟪b, u⟫ + ⟪c, u⟫ + ⟪d, u⟫ = 0 := by
    have h0 : ⟪a + b + c + d, u⟫ = 0 := by rw [hsum, inner_zero_left]
    simpa [inner_add_left] using h0
  have hua : ⟪u, a⟫ = 0 := by rw [real_inner_comm]; linarith
  have hub : ⟪u, b⟫ = 0 := by rw [real_inner_comm]; linarith
  have huc : ⟪u, c⟫ = 0 := by rw [real_inner_comm]; linarith
  have hspan := tetra_span a b c s hs na nb nc iab iac ibc
  have hu : u ∈ Submodule.span ℝ (Set.range ![a, b, c]) := by rw [hspan]; trivial
  rw [Submodule.mem_span_range_iff_exists_fun] at hu
  obtain ⟨g, hg⟩ := hu
  have huu : ⟪u, u⟫ = 0 := by
    calc ⟪u, u⟫ = ⟪u, ∑ i, g i • ![a, b, c] i⟫ := by rw [hg]
    _ = 0 := by
        simp [Fin.sum_univ_three, inner_add_right, real_inner_smul_right, hua, hub, huc]
  have : u = 0 := inner_self_eq_zero.mp huu
  rw [hudef] at this
  linear_combination (norm := module) this
