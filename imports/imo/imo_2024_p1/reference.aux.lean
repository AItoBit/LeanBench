private lemma floor_add_intCast' (x : ℝ) (z : ℤ) : ⌊x + (z : ℝ)⌋ = ⌊x⌋ + z := by
  simp

private lemma floor_intCast' (z : ℤ) : ⌊((z : ℝ))⌋ = z := by
  simp

/-- The Gauss-type closed form used throughout. -/
private lemma sum_aux (a c : ℤ) (m : ℕ) :
    ∑ i ∈ Finset.Icc 1 m, ((i : ℤ) * (2 * a + c) + c * ((i : ℤ) - 1))
      = a * (m : ℤ) * ((m : ℤ) + 1) + c * (m : ℤ) ^ 2 := by
  induction m with
  | zero =>
      rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      simp
  | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      push_cast
      ring
