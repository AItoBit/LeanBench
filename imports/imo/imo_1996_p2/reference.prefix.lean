namespace Imo1996P2

/-- If `s/(s+1)²` is real and `s` is not, then `s` has modulus one. -/
theorem abs_ratio_eq_one {s : ℂ} (h1 : s + 1 ≠ 0) (him : s.im ≠ 0)
    (h : (s / (s + 1) ^ 2).im = 0) : ‖s‖ = 1 := by
  have hd : ((s + 1) ^ 2) ≠ 0 := pow_ne_zero 2 h1
  have hns : Complex.normSq ((s + 1) ^ 2) ≠ 0 := by
    simpa [Complex.normSq_eq_zero] using hd
  rw [Complex.div_im] at h
  have h' : s.im * ((s + 1) ^ 2).re - s.re * ((s + 1) ^ 2).im = 0 := by
    field_simp at h
    linarith
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.one_re, Complex.one_im] at h'
  have hfac : s.im * (1 - s.re * s.re - s.im * s.im) = 0 := by linear_combination h'
  have hsq : s.re * s.re + s.im * s.im = 1 := by
    rcases mul_eq_zero.1 hfac with h0 | h0
    · exact absurd h0 him
    · linarith
  rw [Complex.norm_def, Complex.normSq_apply, hsq, Real.sqrt_one]

/-- The three products always sum to zero. -/
theorem sum_eq_zero (a b c p : ℂ) :
    (a - p) * (b - c) + (b - p) * (c - a) + (c - p) * (a - b) = 0 := by ring
