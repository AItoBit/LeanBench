by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq]
  unfold OnTangent
  constructor
  · rintro ⟨hy, q, ρ, hq0, hρ0, hsum, hq, hρ⟩
    -- the two tangents meet on the line `r x + m y = m r`
    have hne : q - ρ ≠ 0 := by intro h; linarith [sub_eq_zero.1 h]
    have hfac : (q - ρ) * (2 * r * x + (q + ρ) * y - r * (q + ρ)) = 0 := by
      linear_combination hq - hρ
    have hzero : 2 * r * x + (q + ρ) * y - r * (q + ρ) = 0 := by
      rcases mul_eq_zero.1 hfac with h | h
      · exact absurd h hne
      · exact h
    have hline : r * x + m * y = m * r := by
      rw [hsum] at hzero; linarith
    refine ⟨hline, ?_⟩
    -- the tangent-length parameter `u = -qρ` is positive
    have hu : 0 < q ^ 2 - 2 * q * m := by nlinarith
    have hkey : (q ^ 2 - 2 * q * m) * (y - r) = r ^ 2 * (y + r) := by
      linear_combination hq - 2 * q * hline
    by_contra hcon
    rw [not_lt] at hcon
    have hpos : 0 < r ^ 2 * (y + r) := mul_pos (pow_pos hr 2) (by linarith)
    have hnp : 0 ≤ (q ^ 2 - 2 * q * m) * (r - y) := mul_nonneg hu.le (by linarith)
    nlinarith [hkey, hpos, hnp]
  · rintro ⟨hline, hy⟩
    have h1 : 0 < y - r := by linarith
    have h2 : 0 < y + r := by linarith
    set u : ℝ := r ^ 2 * (y + r) / (y - r) with hudef
    have hu0 : 0 < u := div_pos (mul_pos (pow_pos hr 2) h2) h1
    have hukey : u * (y - r) = r ^ 2 * (y + r) := by
      rw [hudef]; field_simp
    set s : ℝ := Real.sqrt (m ^ 2 + u) with hsdef
    have hs : s ^ 2 = m ^ 2 + u := Real.sq_sqrt (by nlinarith [sq_nonneg m])
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hms : m < s := by nlinarith
    have hms' : -m < s := by nlinarith
    refine ⟨by linarith, m - s, m + s, by linarith, by linarith, by ring, ?_, ?_⟩
    · have hq2 : (m - s) ^ 2 - 2 * (m - s) * m = u := by linear_combination hs
      linear_combination (y - r) * hq2 + 2 * (m - s) * hline + hukey
    · have hr2 : (m + s) ^ 2 - 2 * (m + s) * m = u := by linear_combination hs
      linear_combination (y - r) * hr2 + 2 * (m + s) * hline + hukey
