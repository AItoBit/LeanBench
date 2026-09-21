by
  set d : ℕ → ℝ := fun k => (f k : ℝ) - (k : ℝ) with hd
  set w : ℕ → ℝ := fun k => 1 / (k : ℝ) ^ 2 with hwdef
  have hw : ∀ i : ℕ, 1 ≤ i → w (i + 1) ≤ w i := by
    intro i hi
    have hi' : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
    simp only [hwdef]
    push_cast
    apply one_div_le_one_div_of_le <;> nlinarith
  have hwpos : ∀ i : ℕ, 1 ≤ i → 0 ≤ w i := by
    intro i _
    simp only [hwdef]
    positivity
  have hD : ∀ m : ℕ, 0 ≤ ∑ k ∈ Finset.Icc 1 m, d k := by
    intro m
    have h1 : ((∑ k ∈ Finset.Icc 1 m, k : ℕ) : ℝ) ≤ ((∑ k ∈ Finset.Icc 1 m, f k : ℕ) : ℝ) :=
      Nat.cast_le.mpr (sum_le_sum_of_injOn f hinj hpos m)
    push_cast at h1
    simp only [hd, Finset.sum_sub_distrib]
    linarith
  have hmain := weighted_sum_nonneg d w hw hwpos hD n
  have hrw : ∑ k ∈ Finset.Icc 1 n, d k * w k
      = (∑ k ∈ Finset.Icc 1 n, (f k : ℝ) / (k : ℝ) ^ 2)
        - ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / (k : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    simp only [Finset.mem_Icc] at hk
    have hk0 : (k : ℝ) ≠ 0 := by
      have : 1 ≤ k := hk.1
      positivity
    simp only [hd, hwdef]
    field_simp
  linarith [hmain, hrw.le, hrw.ge]
