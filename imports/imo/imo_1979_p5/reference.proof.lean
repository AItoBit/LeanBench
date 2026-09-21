by
  constructor
  · rintro ⟨x, hx, h1, h2, h3⟩
    have hx1 : 0 ≤ x 1 := hx 1 (by decide)
    have hx2 : 0 ≤ x 2 := hx 2 (by decide)
    have hx3 : 0 ≤ x 3 := hx 3 (by decide)
    have hx4 : 0 ≤ x 4 := hx 4 (by decide)
    have hx5 : 0 ≤ x 5 := hx 5 (by decide)
    rw [sum_Icc_one_five] at h1 h2 h3
    norm_num at h1 h2 h3
    -- `a` is non-negative
    have ha0 : 0 ≤ a := by linarith
    -- `Σ(n, n+1) ≥ 0` for `n = 0, 1, 2, 3, 4`
    have k0 : 0 ≤ a * (a - 0) * (a - 1) := by nlinarith
    have k1 : 0 ≤ a * (a - 1) * (a - 4) := by nlinarith
    have k2 : 0 ≤ a * (a - 4) * (a - 9) := by nlinarith
    have k3 : 0 ≤ a * (a - 9) * (a - 16) := by nlinarith
    have k4 : 0 ≤ a * (a - 16) * (a - 25) := by nlinarith
    -- `Σ(0,5) ≤ 0`
    have hu : a ^ 3 - 25 * a ^ 2 ≤ 0 := by nlinarith
    rcases eq_or_lt_of_le ha0 with hpos | hpos
    · exact Or.inl hpos.symm
    -- now `a > 0`
    have hle : a ≤ 25 := by nlinarith
    have c0 := le_or_ge_of_mul_nonneg hpos k0
    have c1 := le_or_ge_of_mul_nonneg hpos k1
    have c2 := le_or_ge_of_mul_nonneg hpos k2
    have c3 := le_or_ge_of_mul_nonneg hpos k3
    have c4 := le_or_ge_of_mul_nonneg hpos k4
    rcases c0 with h | h
    · linarith
    rcases c1 with h' | h'
    · exact Or.inr (Or.inl (le_antisymm h' h))
    rcases c2 with h'' | h''
    · exact Or.inr (Or.inr (Or.inl (le_antisymm h'' h')))
    rcases c3 with h₃ | h₃
    · exact Or.inr (Or.inr (Or.inr (Or.inl (le_antisymm h₃ h''))))
    rcases c4 with h₄ | h₄
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (le_antisymm h₄ h₃)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (le_antisymm hle h₄)))))
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨fun _ => 0, by norm_num, by rw [sum_Icc_one_five]; norm_num,
        by rw [sum_Icc_one_five]; norm_num, by rw [sum_Icc_one_five]; norm_num⟩
    · exact ⟨fun k => if k = 1 then 1 else 0, by intro k _; dsimp only; split <;> norm_num,
        by rw [sum_Icc_one_five]; norm_num, by rw [sum_Icc_one_five]; norm_num,
        by rw [sum_Icc_one_five]; norm_num⟩
    · exact ⟨fun k => if k = 2 then 2 else 0, by intro k _; dsimp only; split <;> norm_num,
        by rw [sum_Icc_one_five]; norm_num, by rw [sum_Icc_one_five]; norm_num,
        by rw [sum_Icc_one_five]; norm_num⟩
    · exact ⟨fun k => if k = 3 then 3 else 0, by intro k _; dsimp only; split <;> norm_num,
        by rw [sum_Icc_one_five]; norm_num, by rw [sum_Icc_one_five]; norm_num,
        by rw [sum_Icc_one_five]; norm_num⟩
    · exact ⟨fun k => if k = 4 then 4 else 0, by intro k _; dsimp only; split <;> norm_num,
        by rw [sum_Icc_one_five]; norm_num, by rw [sum_Icc_one_five]; norm_num,
        by rw [sum_Icc_one_five]; norm_num⟩
    · exact ⟨fun k => if k = 5 then 5 else 0, by intro k _; dsimp only; split <;> norm_num,
        by rw [sum_Icc_one_five]; norm_num, by rw [sum_Icc_one_five]; norm_num,
        by rw [sum_Icc_one_five]; norm_num⟩
