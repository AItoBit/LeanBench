by
  classical
  set x := dist (t.points 1) (t.points 2) with hx
  set y := dist (t.points 0) (t.points 2) with hy
  set z := dist (t.points 0) (t.points 1) with hz
  set g : ℝ := Real.sqrt (gram (t.points 0) (t.points 1) (t.points 2)) with hg
  set a : Fin 3 → ℝ := ![x, y, z] with ha
  have h0 : t.height 0 * x = g :=
    height_mul_dist_eq_sqrt_gram t (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)
      rfl
  have h1 : t.height 1 * y = g :=
    height_mul_dist_eq_sqrt_gram t (i := 1) (j := 0) (k := 2) (by decide) (by decide) (by decide)
      (gram_rot _ _ _).symm
  have h2 : t.height 2 * z = g :=
    height_mul_dist_eq_sqrt_gram t (i := 2) (j := 0) (k := 1) (by decide) (by decide) (by decide)
      (by rw [gram_rot, gram_swap])
  have hheight : ∀ i, t.height i * a i = g := by
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have hxpos : 0 < x := dist_pos.2 (points_ne t (by decide))
  have hypos : 0 < y := dist_pos.2 (points_ne t (by decide))
  have hzpos : 0 < z := dist_pos.2 (points_ne t (by decide))
  have hapos : ∀ i, 0 < a i := by
    intro i
    fin_cases i <;> simpa [ha] using ‹_›
  have hgpos : 0 < g := by
    have h := hheight 0
    have := t.height_pos 0
    have := hapos 0
    nlinarith
  have hinv : ∀ i, (t.height i)⁻¹ = a i / g := by
    intro i
    have h := hheight i
    have hh := t.height_pos i
    field_simp
    linarith [h]
  set S : ℝ := x + y + z with hS
  have hSpos : 0 < S := by positivity
  have hsum : ∑ i, (t.height i)⁻¹ = S / g := by
    rw [Fin.sum_univ_three, hinv 0, hinv 1, hinv 2]
    simp only [ha, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, hS]
    ring
  have hw : t.excenterWeights ∅ = fun i => a i / S := by
    funext i
    simp only [Affine.Simplex.excenterWeights, Affine.Simplex.excenterWeightsUnnorm_empty_apply,
      Pi.smul_apply, smul_eq_mul]
    rw [hsum, hinv i]
    field_simp
  have hsumw : ∑ i, t.excenterWeights ∅ i = 1 := by
    rw [hw, Fin.sum_univ_three]
    simp only [ha, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    field_simp
    rw [hS]
  have hinc := t.incenter_eq_affineCombination
  rw [hw] at hinc
  rw [Finset.affineCombination_eq_linear_combination _ _ _ (hw ▸ hsumw)] at hinc
  have hinc' : t.incenter = (x / S) • t.points 0 + (y / S) • t.points 1 + (z / S) • t.points 2 := by
    rw [hinc]
    simp [Fin.sum_univ_succ, ha, add_assoc]
  rw [hinc', smul_add, smul_add, smul_smul, smul_smul, smul_smul,
    mul_div_cancel₀ _ hSpos.ne', mul_div_cancel₀ _ hSpos.ne', mul_div_cancel₀ _ hSpos.ne']
