by
  unfold IsBlack
  have e1 : ⌊2 * (c₁ : ℝ) - p.1⌋ = 2 * c₁ - ⌊p.1⌋ - 1 := by
    have : (2 : ℝ) * (c₁ : ℝ) - p.1 = -p.1 + ((2 * c₁ : ℤ) : ℝ) := by push_cast; ring
    rw [this, Int.floor_add_intCast, Int.floor_neg, h1]
    omega
  have e2 : ⌊2 * (c₂ : ℝ) - p.2⌋ = 2 * c₂ - ⌊p.2⌋ - 1 := by
    have : (2 : ℝ) * (c₂ : ℝ) - p.2 = -p.2 + ((2 * c₂ : ℤ) : ℝ) := by push_cast; ring
    rw [this, Int.floor_add_intCast, Int.floor_neg, h2]
    omega
  rw [e1, e2]
  constructor
  · rintro ⟨d, hd⟩
    exact ⟨c₁ + c₂ - d - 1, by omega⟩
  · rintro ⟨d, hd⟩
    exact ⟨c₁ + c₂ - d - 1, by omega⟩
