by
  have hsq : ∑ i, (y (σ i)) ^ 2 = ∑ i, (y i) ^ 2 := Equiv.sum_comp σ fun i => (y i) ^ 2
  have hmul := sum_mul_comp_perm_le hx hy σ
  have hexpand : ∀ w : Fin n → ℝ, ∑ i, (x i - w i) ^ 2
      = (∑ i, (x i) ^ 2) - 2 * (∑ i, x i * w i) + ∑ i, (w i) ^ 2 := by
    intro w
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [hz]
  rw [hexpand, hexpand, hsq]
  linarith
