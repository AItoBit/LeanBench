by
  obtain ⟨ha, hb, hc⟩ := h₀
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c),
    mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
    mul_nonneg (sub_nonneg.mpr h₁.le) (sq_nonneg (a - b)),
    mul_nonneg (sub_nonneg.mpr h₂.le) (sq_nonneg (a - c)),
    mul_nonneg (sub_nonneg.mpr h₃.le) (sq_nonneg (b - c))]
