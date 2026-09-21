by
  constructor
  · intro h
    rcases Nat.lt_or_ge x 3 with hlt | hge
    · interval_cases x
      · left
        refine ⟨rfl, ?_⟩
        have h4 : y ^ 2 = 4 := by norm_num at h; linarith
        have hz : (y - 2) * (y + 2) = 0 := by linear_combination h4
        rcases mul_eq_zero.1 hz with h1 | h1
        · left; linarith
        · right; linarith
      · exfalso
        have h11 : y ^ 2 = 11 := by norm_num at h; linarith
        have hb1 : -4 < y := by nlinarith
        have hb2 : y < 4 := by nlinarith
        interval_cases y <;> norm_num at h11
      · exfalso
        have h37 : y ^ 2 = 37 := by norm_num at h; linarith
        have hb1 : -7 < y := by nlinarith
        have hb2 : y < 7 := by nlinarith
        interval_cases y <;> norm_num at h37
    · right
      obtain ⟨k, hk⟩ : ∃ k, x = k + 3 := ⟨x - 3, by omega⟩
      subst hk
      have hrw : (1 : ℤ) + 2 ^ (k + 3) + 2 ^ (2 * (k + 3) + 1)
          = 1 + 8 * 2 ^ k + 128 * ((2 : ℤ) ^ k) ^ 2 := by ring
      rw [hrw] at h
      have hPpos : (0 : ℤ) < 2 ^ k := by positivity
      have hyne : y ≠ 0 := by
        intro h0
        rw [h0] at h
        nlinarith
      rcases lt_or_gt_of_ne hyne with hneg | hpos
      · obtain ⟨hk1, hy23⟩ := key k (-y) (by linarith) (by linear_combination h)
        exact ⟨by omega, Or.inr (by linarith)⟩
      · obtain ⟨hk1, hy23⟩ := key k y hpos h
        exact ⟨by omega, Or.inl hy23⟩
  · rintro (⟨rfl, (rfl | rfl)⟩ | ⟨rfl, (rfl | rfl)⟩) <;> norm_num
