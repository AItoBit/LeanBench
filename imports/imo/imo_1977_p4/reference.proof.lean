by
  constructor
  · -- pair `x` with `x + π/2`: the second harmonic cancels
    have hab : ∀ x : ℝ, (a + b) * Real.cos x + (b - a) * Real.sin x ≤ 2 := by
      intro x
      have h1 := h x
      have h2 := h (x + Real.pi / 2)
      rw [show 2 * (x + Real.pi / 2) = 2 * x + Real.pi from by ring] at h2
      simp only [Real.cos_add, Real.sin_add, Real.cos_pi_div_two, Real.sin_pi_div_two,
        Real.cos_pi, Real.sin_pi] at h2
      linarith
    have := key (by norm_num : (0:ℝ) ≤ 2) hab
    nlinarith [this]
  · -- pair `x` with `x + π`: the first harmonic cancels
    have hAB : ∀ t : ℝ, A * Real.cos t + B * Real.sin t ≤ 1 := by
      intro t
      have h1 := h (t / 2)
      have h2 := h (t / 2 + Real.pi)
      rw [show 2 * (t / 2) = t from by ring] at h1
      rw [show 2 * (t / 2 + Real.pi) = t + 2 * Real.pi from by ring] at h2
      simp only [Real.cos_add, Real.sin_add, Real.cos_pi, Real.sin_pi,
        Real.cos_two_pi, Real.sin_two_pi] at h2
      linarith
    exact key (by norm_num : (0:ℝ) ≤ 1) hAB
