by
  constructor
  · -- Prove BC ≤ k * D
    have h_sin : sin θ ≤ 1 := sin_le_one θ
    have h_PB_le : D * sin θ ≤ D := by
      calc D * sin θ ≤ D * 1 := mul_le_mul_of_nonneg_left h_sin hD
           _ = D := mul_one D
    exact mul_le_mul_of_nonneg_left h_PB_le hk
  · -- Prove equality at θ = π / 2
    intro hθ
    have h_sin_pi_div_two : sin (π / 2) = 1 := sin_pi_div_two
    calc k * (D * sin θ) = k * (D * sin (π / 2)) := by rw [hθ]
         _ = k * (D * 1) := by rw [h_sin_pi_div_two]
         _ = k * D := by ring
