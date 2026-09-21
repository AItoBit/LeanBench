/-- If `a cos t + b sin t ≤ c` for every `t` (and `c ≥ 0`), then `a² + b² ≤ c²`. -/
private lemma key {a b c : ℝ} (hc : 0 ≤ c)
    (h : ∀ t : ℝ, a * Real.cos t + b * Real.sin t ≤ c) : a ^ 2 + b ^ 2 ≤ c ^ 2 := by
  rcases eq_or_lt_of_le (show (0:ℝ) ≤ a ^ 2 + b ^ 2 by positivity) with h0 | h0
  · nlinarith [sq_nonneg c]
  · set r : ℝ := Real.sqrt (a ^ 2 + b ^ 2) with hrdef
    have hr2 : r ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt (by positivity)
    have hrpos : 0 < r := by
      rw [hrdef]
      exact Real.sqrt_pos.mpr h0
    have hrne : r ≠ 0 := hrpos.ne'
    -- `|a| ≤ r`, hence `a / r ∈ [-1, 1]`
    have habs : |a| ≤ r := by
      rcases abs_cases a with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;> nlinarith [sq_nonneg b]
    have hd : |a / r| ≤ 1 := by
      rw [abs_div, abs_of_pos hrpos, div_le_one hrpos]
      exact habs
    obtain ⟨hd2, hd1⟩ := abs_le.mp hd
    -- `sin (arccos (a/r)) = |b| / r`
    have hx2 : 1 - (a / r) ^ 2 = (|b| / r) ^ 2 := by
      rw [div_pow, div_pow, sq_abs]
      field_simp
      linarith [hr2]
    have hsin : Real.sin (Real.arccos (a / r)) = |b| / r := by
      rw [Real.sin_arccos, hx2, Real.sqrt_sq (div_nonneg (abs_nonneg b) hrpos.le)]
    -- a point of the circle with the right coordinates
    obtain ⟨t, hct, hst⟩ : ∃ t : ℝ, Real.cos t = a / r ∧ Real.sin t = b / r := by
      by_cases hb : 0 ≤ b
      · exact ⟨Real.arccos (a / r), Real.cos_arccos hd2 hd1,
          by rw [hsin, abs_of_nonneg hb]⟩
      · refine ⟨-Real.arccos (a / r), ?_, ?_⟩
        · rw [Real.cos_neg]
          exact Real.cos_arccos hd2 hd1
        · rw [Real.sin_neg, hsin, abs_of_neg (not_le.mp hb)]
          ring
    have hle := h t
    rw [hct, hst] at hle
    have hval : a * (a / r) + b * (b / r) = r := by
      field_simp
      nlinarith [hr2]
    rw [hval] at hle
    nlinarith [hle, hrpos, hr2]
