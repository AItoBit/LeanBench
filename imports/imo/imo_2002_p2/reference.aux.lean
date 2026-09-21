lemma gram_of_vectors (u v : V) :
    ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2 = ‖u‖ ^ 2 * ‖v - u‖ ^ 2 - ⟪u, v - u⟫ ^ 2 := by
  rw [norm_sub_sq_real, inner_sub_right, real_inner_self_eq_norm_sq, real_inner_comm v u]
  ring

lemma gram_swap (x y z : V) : gram x y z = gram x z y := by
  simp only [gram, real_inner_comm (y - x) (z - x)]
  ring

lemma gram_rot (x y z : V) : gram x y z = gram y x z := by
  simp only [gram]
  rw [show x - y = -(y - x) by abel, show z - y = (z - x) - (y - x) by abel, norm_neg,
    inner_neg_left, neg_sq]
  exact gram_of_vectors (y - x) (z - x)

/-- An algebraic identity underlying the computation of the height of a triangle. -/
lemma norm_sq_mul_norm_sq_of_inner_eq_zero (u v w : V) (r : ℝ) (hw : w = u + r • (v - u))
    (horth : ⟪v - u, w⟫ = 0) : ‖w‖ ^ 2 * ‖v - u‖ ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2 := by
  have e1 : ‖w‖ ^ 2 = ⟪u, w⟫ := by
    rw [← real_inner_self_eq_norm_sq]
    nth_rewrite 1 [hw]
    rw [inner_add_left, real_inner_smul_left, horth]
    ring
  have e2 : ⟪u, w⟫ = ‖u‖ ^ 2 + r * (⟪u, v⟫ - ‖u‖ ^ 2) := by
    rw [hw, inner_add_right, real_inner_smul_right, inner_sub_right, ← real_inner_self_eq_norm_sq]
  have e3 : ⟪v - u, w⟫ = (⟪u, v⟫ - ‖u‖ ^ 2) + r * ‖v - u‖ ^ 2 := by
    simp only [hw, inner_add_right, real_inner_smul_right, inner_sub_left, inner_sub_right,
      ← real_inner_self_eq_norm_sq, real_inner_comm v u]
    ring
  have hN : ‖v - u‖ ^ 2 = ‖u‖ ^ 2 - 2 * ⟪u, v⟫ + ‖v‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_comm]; ring
  rw [horth] at e3
  rw [e1, e2]
  nlinarith [e3, hN]

/-- The foot of the altitude from a vertex of a triangle lies on the line through the other two
vertices. -/
lemma altitudeFoot_mem_line (t : Triangle ℝ V) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) : t.altitudeFoot i ∈ line[ℝ, t.points j, t.points k] := by
  have h := t.altitudeFoot_mem_affineSpan_image_compl i
  have hset : ({i}ᶜ : Set (Fin 3)) = {j, k} := by
    ext m
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_insert_iff]
    omega
  rw [hset] at h
  simpa [Set.image_insert_eq] using h

/-- The square of (height times the length of the opposite side) is the Gram determinant. -/
lemma height_mul_dist_sq (t : Triangle ℝ V) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    (t.height i * dist (t.points j) (t.points k)) ^ 2 =
      gram (t.points i) (t.points j) (t.points k) := by
  set pi := t.points i
  set pj := t.points j
  set pk := t.points k
  set f := t.altitudeFoot i with hf
  have hmem : f ∈ line[ℝ, pj, pk] := altitudeFoot_mem_line t hij hik hjk
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hmem
  obtain ⟨r, hr⟩ := hmem
  have hfe : f = pj + r • (pk - pj) := by
    rw [← hr]
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    abel
  have h1 : ⟪pj - f, pi - f⟫ = 0 := by
    have := t.inner_vsub_altitudeFoot_vsub_altitudeFoot_eq_zero (i := i) (j := j) hij
    simpa [vsub_eq_sub] using this
  have h2 : ⟪pk - f, pi - f⟫ = 0 := by
    have := t.inner_vsub_altitudeFoot_vsub_altitudeFoot_eq_zero (i := i) (j := k) hik
    simpa [vsub_eq_sub] using this
  have horth : ⟪(pk - pi) - (pj - pi), f - pi⟫ = 0 := by
    have hd : ⟪pk - pj, pi - f⟫ = 0 := by
      have := congrArg₂ (· - ·) h2 h1
      simp only [← inner_sub_left] at this
      simpa using this
    rw [show (pk - pi) - (pj - pi) = pk - pj by abel, show f - pi = -(pi - f) by abel,
      inner_neg_right, hd, neg_zero]
  have key := norm_sq_mul_norm_sq_of_inner_eq_zero (pj - pi) (pk - pi) (f - pi) r
    (by rw [hfe]; abel_nf) horth
  rw [mul_pow, Affine.Simplex.height, dist_eq_norm, dist_eq_norm,
    show pi - f = -(f - pi) by abel, norm_neg,
    show ‖pj - pk‖ = ‖(pk - pi) - (pj - pi)‖ by
      rw [show (pk - pi) - (pj - pi) = -(pj - pk) by abel, norm_neg]]
  exact key

/-- The vertices of a triangle are pairwise distinct. -/
lemma points_ne (t : Triangle ℝ V) {i j : Fin 3} (hij : i ≠ j) : t.points i ≠ t.points j :=
  fun h => hij (t.independent.injective h)

/-- `height i * (length of the side opposite to `i`)` equals `√(gram p₀ p₁ p₂)`, twice the area
of the triangle, whenever the triple `(i, j, k)` is a permutation of `(0, 1, 2)`. -/
lemma height_mul_dist_eq_sqrt_gram (t : Triangle ℝ V) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k)
    (hperm : gram (t.points i) (t.points j) (t.points k)
      = gram (t.points 0) (t.points 1) (t.points 2)) :
    t.height i * dist (t.points j) (t.points k) =
      Real.sqrt (gram (t.points 0) (t.points 1) (t.points 2)) := by
  have hpos : 0 < t.height i * dist (t.points j) (t.points k) :=
    mul_pos (t.height_pos i) (dist_pos.2 (points_ne t hjk))
  have hsq := height_mul_dist_sq t hij hik hjk
  rw [hperm] at hsq
  rw [← hsq, Real.sqrt_sq hpos.le]
