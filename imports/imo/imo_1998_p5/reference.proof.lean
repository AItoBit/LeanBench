by
  obtain ⟨s, rfl⟩ := hRB
  obtain ⟨t, rfl⟩ := hSB
  obtain ⟨u, hu⟩ := eq_add_smul_of_mem_line hRline
  obtain ⟨v, hv⟩ := eq_add_smul_of_mem_line hSline
  obtain ⟨⟨aK, hKB⟩, ⟨bK, hKC⟩⟩ := sub_eq_smul_of_mem_openSegment hK
  obtain ⟨⟨aL, hLC⟩, ⟨bL, hLA⟩⟩ := sub_eq_smul_of_mem_openSegment hL
  obtain ⟨⟨aM, hMA⟩, ⟨bM, hMB⟩⟩ := sub_eq_smul_of_mem_openSegment hM
  -- self inner products
  have hkk : ⟪K - I, K - I⟫ = r ^ 2 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, dist_comm, hIK]
  have hll : ⟪L - I, L - I⟫ = r ^ 2 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, dist_comm, hIL]
  have hmm : ⟪M - I, M - I⟫ = r ^ 2 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, dist_comm, hIM]
  have hknz : K - I ≠ 0 := by
    intro h; rw [h, inner_zero_left] at hkk; nlinarith
  have hlnz : L - I ≠ 0 := by
    intro h; rw [h, inner_zero_left] at hll; nlinarith
  have hmnz : M - I ≠ 0 := by
    intro h; rw [h, inner_zero_left] at hmm; nlinarith
  -- the reversed tangency conditions
  have hKt' : ⟪K - I, B - C⟫ = 0 := by
    rw [show B - C = -(C - B) by abel, inner_neg_right, hKt, neg_zero]
  have hLt' : ⟪L - I, C - A⟫ = 0 := by
    rw [show C - A = -(A - C) by abel, inner_neg_right, hLt, neg_zero]
  have hMt' : ⟪M - I, A - B⟫ = 0 := by
    rw [show A - B = -(B - A) by abel, inner_neg_right, hMt, neg_zero]
  -- the six vertex-to-touch-point relations
  have hbk : ⟪B - I, K - I⟫ = r ^ 2 := inner_vertex_touch hIK hKt ⟨aK, hKB⟩
  have hck : ⟪C - I, K - I⟫ = r ^ 2 := inner_vertex_touch hIK hKt' ⟨bK, hKC⟩
  have hcl : ⟪C - I, L - I⟫ = r ^ 2 := inner_vertex_touch hIL hLt ⟨aL, hLC⟩
  have hal : ⟪A - I, L - I⟫ = r ^ 2 := inner_vertex_touch hIL hLt' ⟨bL, hLA⟩
  have ham : ⟪A - I, M - I⟫ = r ^ 2 := inner_vertex_touch hIM hMt ⟨aM, hMA⟩
  have hbm : ⟪B - I, M - I⟫ = r ^ 2 := inner_vertex_touch hIM hMt' ⟨bM, hMB⟩
  -- the touch points are pairwise distinct
  have hKM : K ≠ M := by
    intro h
    refine hABC (collinear_of_perp (n := K - I) hknz ?_ ?_)
    · rw [h]; exact hMt
    · rw [show C - A = (C - B) + (B - A) by abel, inner_add_right, hKt, h, hMt]; ring
  have hKL : K ≠ L := by
    intro h
    refine hABC (collinear_of_perp (n := K - I) hknz ?_ ?_)
    · rw [show B - A = -((C - B) + (A - C)) by abel, inner_neg_right, inner_add_right, hKt,
        h, hLt]; ring
    · rw [h]; exact hLt'
  have hLM : L ≠ M := by
    intro h
    refine hABC (collinear_of_perp (n := L - I) hlnz ?_ ?_)
    · rw [h]; exact hMt
    · exact hLt'
  -- the inner product bounds
  have hp : -r ^ 2 < ⟪K - I, M - I⟫ := neg_sq_lt_inner hr hkk hmm hbk hbm
  have hq : -r ^ 2 < ⟪K - I, L - I⟫ := neg_sq_lt_inner hr hkk hll hck hcl
  have hw : -r ^ 2 < ⟪L - I, M - I⟫ := neg_sq_lt_inner hr hll hmm hal ham
  have hp' : ⟪K - I, M - I⟫ < r ^ 2 :=
    inner_lt_sq hkk hmm (fun h => hKM (by simpa [sub_left_inj] using h))
  have hq' : ⟪K - I, L - I⟫ < r ^ 2 :=
    inner_lt_sq hkk hll (fun h => hKL (by simpa [sub_left_inj] using h))
  have hw' : ⟪L - I, M - I⟫ < r ^ 2 :=
    inner_lt_sq hll hmm (fun h => hLM (by simpa [sub_left_inj] using h))
  -- pass to coordinates
  rw [inner_sub_coord] at hbk hck hcl hal ham hbm hp hq hw hp' hq' hw' hkk hll hmm
  have hk2 : (K 0 - I 0) ^ 2 + (K 1 - I 1) ^ 2 = r ^ 2 := by linear_combination hkk
  have hl2 : (L 0 - I 0) ^ 2 + (L 1 - I 1) ^ 2 = r ^ 2 := by linear_combination hll
  have hm2 : (M 0 - I 0) ^ 2 + (M 1 - I 1) ^ 2 = r ^ 2 := by linear_combination hmm
  have hR0 : (B 0 - I 0) + s * ((K 0 - I 0) - (M 0 - I 0)) =
      (L 0 - I 0) + u * ((M 0 - I 0) - (L 0 - I 0)) := by
    have h := congrFun (congrArg (fun z => (z : EuclideanSpace ℝ (Fin 2)).ofLp) hu) 0
    simp at h
    linear_combination h
  have hR1 : (B 1 - I 1) + s * ((K 1 - I 1) - (M 1 - I 1)) =
      (L 1 - I 1) + u * ((M 1 - I 1) - (L 1 - I 1)) := by
    have h := congrFun (congrArg (fun z => (z : EuclideanSpace ℝ (Fin 2)).ofLp) hu) 1
    simp at h
    linear_combination h
  have hS0 : (B 0 - I 0) + t * ((K 0 - I 0) - (M 0 - I 0)) =
      (L 0 - I 0) + v * ((K 0 - I 0) - (L 0 - I 0)) := by
    have h := congrFun (congrArg (fun z => (z : EuclideanSpace ℝ (Fin 2)).ofLp) hv) 0
    simp at h
    linear_combination h
  have hS1 : (B 1 - I 1) + t * ((K 1 - I 1) - (M 1 - I 1)) =
      (L 1 - I 1) + v * ((K 1 - I 1) - (L 1 - I 1)) := by
    have h := congrFun (congrArg (fun z => (z : EuclideanSpace ℝ (Fin 2)).ofLp) hv) 1
    simp at h
    linear_combination h
  have hcore := coord_core r (K 0 - I 0) (K 1 - I 1) (L 0 - I 0) (L 1 - I 1)
    (M 0 - I 0) (M 1 - I 1) (B 0 - I 0) (B 1 - I 1) s t u v hk2 hl2 hm2
    (by linear_combination hbk) (by linear_combination hbm)
    (by linear_combination hp) (by linear_combination hq) (by linear_combination hw)
    (by linear_combination hp') (by linear_combination hq') (by linear_combination hw')
    hR0 hR1 hS0 hS1
  -- conclude
  have hang : EuclideanGeometry.angle (B + s • (K - M)) I (B + t • (K - M)) =
      InnerProductGeometry.angle ((B + s • (K - M)) - I) ((B + t • (K - M)) - I) := by
    simp [EuclideanGeometry.angle, vsub_eq_sub]
  rw [hang]
  refine angle_lt_pi_div_two_of_inner_pos ?_
  rw [inner_sub_coord]
  have hval : ((B + s • (K - M)) 0 - I 0) * ((B + t • (K - M)) 0 - I 0) +
      ((B + s • (K - M)) 1 - I 1) * ((B + t • (K - M)) 1 - I 1) = r ^ 2 := by
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    linear_combination hcore
  rw [hval]
  positivity

/-! ### The hypotheses are consistent

We exhibit an explicit configuration satisfying all the hypotheses of `candidate`:
the isosceles triangle `A = (0, 5/3)`, `B = (-2, -1)`, `C = (2, -1)`, whose incircle is the
unit circle centred at the origin, touching the sides at `K = (0, -1)`, `L = (4/5, 3/5)` and
`M = (-4/5, 3/5)`.  Here `R = (-14/5, 3/5)` and `S = (-1, -3)`. -/
