by
  constructor
  · have h := lower_pow4 n (by omega)
    have h' : ((2 : ℝ) ^ ((n : ℝ) ^ 2 / 4)) ^ (4 : ℕ) < (f (2 ^ n) : ℝ) ^ (4 : ℕ) := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ ((n : ℝ) ^ 2 / 4)) 4, ← Real.rpow_mul (by norm_num),
        show (n : ℝ) ^ 2 / 4 * ((4 : ℕ) : ℝ) = ((n ^ 2 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast]
      exact_mod_cast h
    exact lt_of_pow_lt_pow_left₀ 4 (by positivity) h'
  · have h := upper_sq n hn
    have h' : (f (2 ^ n) : ℝ) ^ (2 : ℕ) < ((2 : ℝ) ^ ((n : ℝ) ^ 2 / 2)) ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ ((n : ℝ) ^ 2 / 2)) 2, ← Real.rpow_mul (by norm_num),
        show (n : ℝ) ^ 2 / 2 * ((2 : ℕ) : ℝ) = ((n ^ 2 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast]
      exact_mod_cast h
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h'
