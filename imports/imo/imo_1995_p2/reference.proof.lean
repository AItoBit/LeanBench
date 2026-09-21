by
  rcases h₀ with ⟨ha, hb, hc⟩
  have hcauchy := three_term_cauchy a b c ha hb hc
  have hamgm := three_le_pairwise_sum a b c ha hb hc h₁
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hinva : 1 / a = b * c := by
    apply (div_eq_iff ha0).2
    nlinarith [h₁]
  have hinvb : 1 / b = c * a := by
    apply (div_eq_iff hb0).2
    nlinarith [h₁]
  have hinvc : 1 / c = a * b := by
    apply (div_eq_iff hc0).2
    nlinarith [h₁]
  have hsum : 0 < a * b + b * c + c * a := by positivity
  have hquotient :
      ((1 / a + 1 / b + 1 / c) ^ 2) /
          (a * (b + c) + b * (c + a) + c * (a + b)) =
        (a * b + b * c + c * a) / 2 := by
    rw [hinva, hinvb, hinvc]
    field_simp [ne_of_gt hsum]
    ring
  rw [hquotient] at hcauchy
  linarith
