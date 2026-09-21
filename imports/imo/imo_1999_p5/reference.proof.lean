by
  have hnn : dot n n = 1 := by rw [dot_self, hn]; norm_num
  have h1' : dot O₁ O₁ = (R - r₁) ^ 2 := by rw [dot_self, h1]
  have h2' : dot O₂ O₂ = (R - r₂) ^ 2 := by rw [dot_self, h2]
  -- `⟪O₂, n⟫ - ⟪O₁, n⟫ = r₁`
  have hdotdiff : dot O₂ n - dot O₁ n = r₁ := by
    have e := dot_sub_left O₂ O₁ n
    rw [h12, dot_real_smul, hnn] at e
    linarith
  -- `⟪X, O₂⟫ - ⟪X, O₁⟫ = r₁ t`
  have hXO : dot X O₂ - dot X O₁ = r₁ * t := by
    have e := dot_sub_left O₂ O₁ X
    rw [h12, dot_real_smul, dot_comm n X, hXt] at e
    rw [dot_comm X O₂, dot_comm X O₁]
    linarith
  -- the radical-axis condition pins down `t`
  rw [norm_sub_sq, norm_sub_sq, h1', h2'] at hXrad
  have ht : r₁ * t = R * (r₁ - r₂) := by nlinarith [hXrad, hXO]
  -- conclude
  have hs : s = dot O₁ n + (r₁ / R) * t := by linarith
  have h3 : (r₁ / R) * t = r₁ - r₂ := by
    rw [div_mul_eq_mul_div, div_eq_iff hR.ne']
    linarith
  have hfinal : dot O₂ n - s = r₂ := by
    rw [hs, h3]
    linarith
  rw [hfinal, abs_of_pos hr₂]
