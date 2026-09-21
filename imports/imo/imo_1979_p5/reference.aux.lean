/-- Expansion of a sum over `{1, …, 5}`. -/
lemma sum_Icc_one_five (f : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc (1 : ℕ) 5, f k = f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp [Finset.sum_Icc_succ_top]

/-- If `a > 0` and `a * (a - p) * (a - q) ≥ 0`, then `a ≤ p` or `q ≤ a`. -/
lemma le_or_ge_of_mul_nonneg {a p q : ℝ} (ha : 0 < a)
    (h : 0 ≤ a * (a - p) * (a - q)) : a ≤ p ∨ q ≤ a := by
  rcases le_or_gt a p with hp | hp
  · exact Or.inl hp
  · right
    by_contra hq
    push_neg at hq
    exact absurd h (not_le.mpr (mul_neg_of_pos_of_neg (mul_pos ha (sub_pos.mpr hp))
      (by linarith)))
