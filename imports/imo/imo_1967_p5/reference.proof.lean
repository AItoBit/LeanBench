by
  constructor
  · -- Odd powers cancel out exactly
    rw [h₁, h₂, h₃, h₄]
    have eq1 := neg_pow_odd a₈ k
    have eq2 := neg_pow_odd a₇ k
    have eq3 := neg_pow_odd a₆ k
    have eq4 := neg_pow_odd a₅ k
    rw [eq1, eq2, eq3, eq4]
    ring
  · -- Even powers are sums of non-negative reals
    have eq1 := pow_even_nonneg a₁ k
    have eq2 := pow_even_nonneg a₂ k
    have eq3 := pow_even_nonneg a₃ k
    have eq4 := pow_even_nonneg a₄ k
    have eq5 := pow_even_nonneg a₅ k
    have eq6 := pow_even_nonneg a₆ k
    have eq7 := pow_even_nonneg a₇ k
    have eq8 := pow_even_nonneg a₈ k
    linarith
