  have h3 : ∀ {x : ℝ}, 0 < x → (x ^ (3 : ℝ)⁻¹) ^ 3 = x := fun hx =>
    show ↑3 = (3 : ℝ) by simp ▸ rpow_inv_natCast_pow hx.le three_ne_zero
  calc
    1 ≤ _ := imo2001_q2' (rpow_pos_of_pos ha _) (rpow_pos_of_pos hb _) (rpow_pos_of_pos hc _)
    _ = _ := by rw [h3 ha, h3 hb, h3 hc]
