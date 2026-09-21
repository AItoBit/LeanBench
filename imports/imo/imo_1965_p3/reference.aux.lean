theorem ratio_pos {k : ℝ} (hk : 0 < k) : 0 < ratio k := by
  unfold ratio
  positivity

theorem one_sub_ratio {k : ℝ} (hk : 0 < k) : 1 - ratio k = 1 / (k + 1) := by
  unfold ratio
  have : k + 1 ≠ 0 := by linarith
  field_simp; ring

theorem volLower_eq (k : ℝ) (V : ℝ) :
    volLower k V = ((ratio k) ^ 3 + 3 * (ratio k) ^ 2 * (1 - ratio k)) * V := by
  unfold volLower volTetra volPrism
  ring

/-- The volume of `ABWXYZ` expressed directly in terms of `k` and `V`. -/
theorem volLower_formula {k : ℝ} (hk : 0 < k) (V : ℝ) :
    volLower k V = (k ^ 3 + 3 * k ^ 2) / (k + 1) ^ 3 * V := by
  rw [volLower_eq, one_sub_ratio hk]
  unfold ratio
  have hk1 : k + 1 ≠ 0 := by linarith
  have : (k / (k + 1)) ^ 3 + 3 * (k / (k + 1)) ^ 2 * (1 / (k + 1))
      = (k ^ 3 + 3 * k ^ 2) / (k + 1) ^ 3 := by
    field_simp
  rw [this]

/-- The volume of the complementary solid expressed directly in terms of `k` and `V`. -/
theorem volUpper_formula {k : ℝ} (hk : 0 < k) (V : ℝ) :
    volUpper k V = (3 * k + 1) / (k + 1) ^ 3 * V := by
  unfold volUpper
  rw [volLower_formula hk]
  have hk1 : k + 1 ≠ 0 := by linarith
  have : 1 - (k ^ 3 + 3 * k ^ 2) / (k + 1) ^ 3 = (3 * k + 1) / (k + 1) ^ 3 := by
    field_simp; ring
  calc V - (k ^ 3 + 3 * k ^ 2) / (k + 1) ^ 3 * V
    _ = (1 - (k ^ 3 + 3 * k ^ 2) / (k + 1) ^ 3) * V := by ring
    _ = (3 * k + 1) / (k + 1) ^ 3 * V := by rw [this]

/-! ## Main Theorem -/
