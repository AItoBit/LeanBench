lemma K_nonneg
    (x y : ℝ) :
    0 ≤ K x y := by
  unfold K
  exact Real.sqrt_nonneg _

lemma K_self
    (x : ℝ) :
    K x x = 0 := by
  unfold K
  simp

lemma K_symm
    (x y : ℝ) :
    K x y = K y x := by
  unfold K
  rw [abs_sub_comm]

/-!
============================================================
2. The two sums from the problem
============================================================
-/

lemma K_pos_pos
    (x y : ℝ) :
    K x y =
      Real.sqrt |x - y| := by
  rfl

lemma K_pos_neg
    (x y : ℝ) :
    K x (-y) =
      Real.sqrt |x + y| := by

  unfold K

  have h :
      x - (-y) = x + y := by
    ring

  rw [h]

lemma K_neg_pos
    (x y : ℝ) :
    K (-x) y =
      Real.sqrt |x + y| := by

  unfold K

  have h :
      -x - y =
        -(x + y) := by
    ring

  rw [h]

  rw [abs_neg]

lemma K_neg_neg
    (x y : ℝ) :
    K (-x) (-y) =
      Real.sqrt |x - y| := by

  unfold K

  have h :
      -x - (-y) =
        -(x - y) := by
    ring

  rw [h]

  rw [abs_neg]

/-!
============================================================
4. Signed block
============================================================
-/

lemma signedBlock_eq
    {n : ℕ}
    (x : Fin n → ℝ)
    (i j : Fin n) :
    signedBlock x i j
      =
    2 * Real.sqrt |x i - x j|
      -
    2 * Real.sqrt |x i + x j| := by

  unfold signedBlock

  rw [
    K_pos_pos,
    K_pos_neg,
    K_neg_pos,
    K_neg_neg
  ]

  ring

/-!
============================================================
5. Signed energy
============================================================
-/

lemma signedEnergy_eq
    {n : ℕ}
    (x : Fin n → ℝ) :
    signedEnergy x =
      2 * lhs x - 2 * rhs x := by

  unfold signedEnergy

  simp_rw [signedBlock_eq]

  unfold lhs rhs

  simp_rw [Finset.sum_sub_distrib]

  simp_rw [← Finset.mul_sum]

/-!
============================================================
7. Analytic negative-type statement
============================================================
-/

/-
This is the nontrivial analytic input.

It says that the signed energy obtained from the points
xᵢ and -xᵢ with coefficients +1 and -1 is nonpositive.

This is the specialization of conditional negative
definiteness of

    K(x,y) = √|x-y|

needed for the olympiad problem.
-/

lemma lhs_le_rhs_of_signedEnergy
    {n : ℕ}
    (x : Fin n → ℝ)
    (h :
      signedEnergy x ≤ 0) :
    lhs x ≤ rhs x := by

  have heq :
      signedEnergy x =
        2 * lhs x - 2 * rhs x :=
    signedEnergy_eq x

  rw [heq] at h

  linarith

/-!
============================================================
9. Main theorem from negative type
============================================================
-/

theorem imo2021_p2_of_negative_type
    (hneg :
      NegativeTypeSqrtKernel) :
    ∀ {n : ℕ}
      (x : Fin n → ℝ),
      lhs x ≤ rhs x := by

  intro n x

  have henergy :
      signedEnergy x ≤ 0 :=
    hneg x

  exact
    lhs_le_rhs_of_signedEnergy
      x
      henergy

/-!
============================================================
10. Expanded final statement
============================================================
-/

theorem imo2021_p2
    (hneg :
      NegativeTypeSqrtKernel)
    {n : ℕ}
    (x : Fin n → ℝ) :
    (∑ i : Fin n,
      ∑ j : Fin n,
        Real.sqrt |x i - x j|)
      ≤
    (∑ i : Fin n,
      ∑ j : Fin n,
        Real.sqrt |x i + x j|) := by

  have h :
      lhs x ≤ rhs x :=
    imo2021_p2_of_negative_type
      hneg
      x

  exact h

/-!
============================================================
11. Version using the expanded energy inequality directly
============================================================
-/
