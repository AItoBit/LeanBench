by
  constructor
  · rintro ⟨k, hk, hak⟩
    have ha2 : 0 < a ^ 2 := by positivity
    have hb1 : 1 ≤ b := by omega
    rcases eq_or_lt_of_le hb1 with h | hb2
    · -- `b = 1`
      have hbe : b = 1 := h.symm
      subst hbe
      refine ⟨k, hk, Or.inl ⟨?_, rfl⟩⟩
      exact mul_right_cancel₀ (ne_of_gt ha) (by linear_combination hak)
    · -- `b > 1`: introduce the other root
      obtain ⟨a', ha'⟩ : ∃ a', a' = 2 * k * b ^ 2 - a := ⟨_, rfl⟩
      have hroot : a * a' = k * (b ^ 3 - 1) := by rw [ha']; linear_combination -hak
      have hb3 : 0 < b ^ 3 - 1 := by nlinarith
      have ha'pos : 0 < a' := by
        rcases lt_trichotomy a' 0 with h1 | h1 | h1
        · nlinarith [hroot, hk, hb3, ha, h1]
        · rw [h1, mul_zero] at hroot
          nlinarith [hk, hb3]
        · exact h1
      rcases le_total a a' with hcase | hcase
      · -- `a ≤ a'` : the family `(n, 2n)`
        have hle : a ^ 2 ≤ k * (b ^ 3 - 1) := by
          rw [← hroot]
          nlinarith [hcase, ha]
        obtain ⟨hbe, -⟩ := key ha hb2 hk hak hle
        exact ⟨a, ha, Or.inr (Or.inl ⟨rfl, hbe⟩)⟩
      · -- `a' < a` : the family `(8n⁴ - n, 2n)`
        have hak' : a' ^ 2 = k * (2 * a' * b ^ 2 - b ^ 3 + 1) := by
          rw [ha']; linear_combination hak
        have hle' : a' ^ 2 ≤ k * (b ^ 3 - 1) := by
          rw [← hroot]
          nlinarith [hcase, ha'pos]
        obtain ⟨hbe, hke⟩ := key ha'pos hb2 hk hak' hle'
        refine ⟨a', ha'pos, Or.inr (Or.inr ⟨?_, hbe⟩)⟩
        refine mul_right_cancel₀ (ne_of_gt ha'pos) ?_
        rw [hroot, hke, hbe]
        ring
  · rintro ⟨n, hn, (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)⟩
    · exact ⟨n, hn, by rw [h1, h2]; ring⟩
    · exact ⟨n ^ 2, pow_pos hn 2, by rw [h1, h2]; ring⟩
    · exact ⟨n ^ 2, pow_pos hn 2, by rw [h1, h2]; ring⟩
