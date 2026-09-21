by
  have h_alg := imo1968_p3_algebra s a b c 0 x hΔ.symm h_sum
  rw [mul_zero] at h_alg
  
  have h_sq_nonneg : ∀ i ∈ s, (0 : ℝ) ≤ (2 * a * x i + b - 1)^2 := fun i _ ↦ sq_nonneg _
  have h_zero : ∀ i ∈ s, (2 * a * x i + b - 1)^2 = 0 := by
    intro i hi
    exact (sum_eq_zero_iff_of_nonneg h_sq_nonneg).mp h_alg i hi
  
  intro i hi
  have hi_zero := h_zero i hi
  have hi_linear : 2 * a * x i + b - 1 = 0 := sq_eq_zero_iff.mp hi_zero
  have h2a : 2 * a ≠ 0 := mul_ne_zero (by norm_num) ha
  
  calc x i = (2 * a * x i) / (2 * a) := (mul_div_cancel_left₀ (x i) h2a).symm
     _ = (1 - b) / (2 * a) := by
        congr 1
        linarith
