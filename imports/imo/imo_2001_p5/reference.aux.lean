/-- The trigonometric core of the problem: the difference of the two sides of the equation
`1 + sin 30° / sin (150° - 2x) = (sin x + sin 60°) / sin (120° - x)`, cleared of denominators,
factors as `sin (x/2 + 30°) * cos (3x/2 + 30°) * (2 cos x - 1)`. -/
theorem trig_factorization (x : ℝ) :
    sin (5 * π / 6 - 2 * x) * sin (2 * π / 3 - x) + sin (π / 6) * sin (2 * π / 3 - x)
        - (sin x + sin (π / 3)) * sin (5 * π / 6 - 2 * x)
      = sin (x / 2 + π / 6) * cos (3 * x / 2 + π / 6) * (2 * cos x - 1) := by
  obtain ⟨t, rfl⟩ : ∃ t : ℝ, x = 2 * t := ⟨x / 2, by ring⟩
  have e1 : sin (2 * π / 3 - 2 * t) = 2 * sin (t + π / 6) * cos (t + π / 6) := by
    rw [show 2 * π / 3 - 2 * t = π - (2 * (t + π / 6)) by ring, Real.sin_pi_sub,
      Real.sin_two_mul]
  have e2 : sin (2 * t) + sin (π / 3) = 2 * sin (t + π / 6) * cos (t - π / 6) := by
    rw [Real.sin_add_sin]
    ring_nf
  have e3 : cos (t + π / 6) - cos (t - π / 6) = -sin t := by
    rw [Real.cos_sub_cos, show (t + π / 6 + (t - π / 6)) / 2 = t by ring,
      show (t + π / 6 - (t - π / 6)) / 2 = π / 6 by ring, Real.sin_pi_div_six]
    ring
  have e4 : cos (5 * t - 5 * π / 6) - cos (5 * π / 6 - 3 * t)
      = 2 * sin t * sin (5 * π / 6 - 4 * t) := by
    rw [Real.cos_sub_cos]
    have : (5 * t - 5 * π / 6 - (5 * π / 6 - 3 * t)) / 2 = -(5 * π / 6 - 4 * t) := by ring
    rw [this, Real.sin_neg]
    have : (5 * t - 5 * π / 6 + (5 * π / 6 - 3 * t)) / 2 = t := by ring
    rw [this]
    ring
  have e5 : cos (5 * t - 5 * π / 6) = -cos (5 * t + π / 6) := by
    rw [show 5 * t - 5 * π / 6 = -(π - (5 * t + π / 6)) by ring, Real.cos_neg, Real.cos_pi_sub]
  have e6 : cos (5 * π / 6 - 3 * t) = -cos (3 * t + π / 6) := by
    rw [show 5 * π / 6 - 3 * t = π - (3 * t + π / 6) by ring, Real.cos_pi_sub]
  have e7 : cos (t + π / 6) + cos (5 * t + π / 6) = 2 * cos (3 * t + π / 6) * cos (2 * t) := by
    rw [Real.cos_add_cos]
    have h1 : (t + π / 6 + (5 * t + π / 6)) / 2 = 3 * t + π / 6 := by ring
    have h2 : (t + π / 6 - (5 * t + π / 6)) / 2 = -(2 * t) := by ring
    rw [h1, h2, Real.cos_neg]
  have hx : 2 * t / 2 = t := by ring
  rw [hx, show 5 * π / 6 - 2 * (2 * t) = 5 * π / 6 - 4 * t by ring,
    show 3 * (2 * t) / 2 = 3 * t by ring, Real.sin_pi_div_six]
  -- now combine
  have key : sin (5 * π / 6 - 4 * t) * sin (2 * π / 3 - 2 * t)
      + 1 / 2 * sin (2 * π / 3 - 2 * t)
      - (sin (2 * t) + sin (π / 3)) * sin (5 * π / 6 - 4 * t)
      = sin (t + π / 6) * (cos (t + π / 6) - 2 * (sin t * sin (5 * π / 6 - 4 * t))) := by
    rw [e1, e2]; linear_combination (2 * sin (5 * π / 6 - 4 * t) * sin (t + π / 6)) * e3
  rw [key]
  have key2 : cos (t + π / 6) - 2 * (sin t * sin (5 * π / 6 - 4 * t))
      = cos (3 * t + π / 6) * (2 * cos (2 * t) - 1) := by
    linear_combination e4 - e5 + e6 + e7
  rw [key2]
  ring
