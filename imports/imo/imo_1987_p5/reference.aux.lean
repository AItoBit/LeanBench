lemma not_isSquare_one_add_sq (m : ℕ) (hm : 1 ≤ m) : ¬ IsSquare (1 + m ^ 2) := by
  rintro ⟨s, hs⟩
  rcases le_or_gt s m with h | h
  · have := Nat.mul_le_mul h h
    nlinarith
  · have h' : m + 1 ≤ s := h
    have := Nat.mul_le_mul h' h'
    nlinarith

lemma irrational_eDist {a b : ℕ} (hab : a ≠ b) :
    Irrational (eDist ((a : ℝ), (a : ℝ) ^ 2) ((b : ℝ), (b : ℝ) ^ 2)) := by
  simp only [eDist]
  have key : ((a : ℝ) - b) ^ 2 + ((a : ℝ) ^ 2 - (b : ℝ) ^ 2) ^ 2
      = ((a : ℝ) - b) ^ 2 * ((1 + (a + b) ^ 2 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [key, Real.sqrt_mul' _ (Nat.cast_nonneg _), Real.sqrt_sq_eq_abs]
  have hN : Irrational (Real.sqrt ((1 + (a + b) ^ 2 : ℕ) : ℝ)) := by
    rw [irrational_sqrt_natCast_iff]
    exact not_isSquare_one_add_sq (a + b) (by omega)
  have hq : |(a : ℝ) - b| = ((|(a : ℚ) - b| : ℚ) : ℝ) := by
    push_cast <;> ring
  have hab' : (a : ℚ) ≠ b := by exact_mod_cast hab
  have hq0 : |(a : ℚ) - b| ≠ 0 := (abs_pos.mpr (sub_ne_zero.mpr hab')).ne'
  rw [hq]
  exact hN.ratCast_mul hq0

lemma triArea_facts {a b c : ℕ} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    triArea ((a : ℝ), (a : ℝ) ^ 2) ((b : ℝ), (b : ℝ) ^ 2) ((c : ℝ), (c : ℝ) ^ 2) ≠ 0 ∧
      ∃ q : ℚ,
        triArea ((a : ℝ), (a : ℝ) ^ 2) ((b : ℝ), (b : ℝ) ^ 2) ((c : ℝ), (c : ℝ) ^ 2) = q := by
  have key : triArea ((a : ℝ), (a : ℝ) ^ 2) ((b : ℝ), (b : ℝ) ^ 2) ((c : ℝ), (c : ℝ) ^ 2) =
      |((b : ℝ) - a) * ((c : ℝ) - a) * ((c : ℝ) - b)| / 2 := by
    simp only [triArea]
    rw [show ((b : ℝ) - a) * ((c : ℝ) ^ 2 - (a : ℝ) ^ 2) - ((c : ℝ) - a) * ((b : ℝ) ^ 2 - (a : ℝ) ^ 2)
        = ((b : ℝ) - a) * ((c : ℝ) - a) * ((c : ℝ) - b) by ring]
  rw [key]
  have hab' : (b : ℝ) - a ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hab.symm)
  have hac' : (c : ℝ) - a ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hac.symm)
  have hbc' : (c : ℝ) - b ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hbc.symm)
  have hprod : ((b : ℝ) - a) * ((c : ℝ) - a) * ((c : ℝ) - b) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hab' hac') hbc'
  refine ⟨(div_pos (abs_pos.mpr hprod) two_pos).ne',
    |((b : ℚ) - a) * ((c : ℚ) - a) * ((c : ℚ) - b)| / 2, ?_⟩
  push_cast <;> ring
