by
  -- eliminating `r₁ - r₂` between the `M`-relations and the `N`-relations
  have hstar : n₂ * (2 * m₁ - a - b) = m₂ * (2 * n₁ - a - b) := by
    have h1 : (b - a) * (n₂ * (2 * m₁ - a - b) - m₂ * (2 * n₁ - a - b)) = 0 := by
      linear_combination n₂ * hM1 - n₂ * hM2 - m₂ * hN1 + m₂ * hN2
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd (by linarith : a = b) hab
    · linarith
  -- `M` is the midpoint of `PQ`
  have hkey : px + qx = 2 * m₁ := by
    have h2 : n₂ * (px + qx - a - b) = n₂ * (2 * m₁ - a - b) := by
      linear_combination -hP - hQ - hstar
    have h3 := mul_left_cancel₀ hn₂ h2
    linarith
  -- `E` is the reflection of `M` in `AB`
  have hey : ey = -m₂ := by
    have h1 : (a - b) * (ey + m₂) = 0 := by linear_combination hE1 - hE2
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd (by linarith : a = b) hab
    · linarith
  have hex : ex = m₁ := by
    have h1 : m₂ * (ex - m₁) = 0 := by
      rw [hey] at hE1
      linear_combination -hE1
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd h hm₂
    · linarith
  -- hence the two distances agree
  have hsq : Complex.normSq ((⟨ex, ey⟩ : ℂ) - (⟨px, m₂⟩ : ℂ))
      = Complex.normSq ((⟨ex, ey⟩ : ℂ) - (⟨qx, m₂⟩ : ℂ)) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hex, hey]
    linear_combination (px - qx) * hkey
  rw [Complex.dist_eq, Complex.dist_eq, Complex.norm_def, Complex.norm_def, hsq]
