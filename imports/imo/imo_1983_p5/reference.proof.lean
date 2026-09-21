by
  
  -- 1. Extract k1 in terms of r from the y-coordinate of M
  have hH1 : k1 - (1 - r / 2) = 0 := by
    have h_mult : (k1 - (1 - r / 2)) * s3 = 0 := by
      calc (k1 - (1 - r / 2)) * s3 = k1 * s3 - (1 - r) * s3 - r * s3 / 2 := by ring
        _ = ((1 - r) * s3 + r * s3 / 2) - (1 - r) * s3 - r * s3 / 2 := by rw [hM_y]
        _ = 0 := by ring
    cases mul_eq_zero.mp h_mult with
    | inl h => exact h
    | inr h => exact False.elim (hs3 h)

  -- 2. Extract k2 in terms of r from the y-coordinate of N
  have hH3 : k2 - (1 - r) / 2 = 0 := by
    have h_mult : (k2 - (1 - r) / 2) * s3 = 0 := by
      calc (k2 - (1 - r) / 2) * s3 = k2 * s3 - (1 - r) * s3 / 2 := by ring
        _ = (1 - r) * s3 / 2 - (1 - r) * s3 / 2 := by rw [hN_y]
        _ = 0 := by ring
    cases mul_eq_zero.mp h_mult with
    | inl h => exact h
    | inr h => exact False.elim (hs3 h)

  -- 3. Rearrange the x-coordinate equations to equal 0
  have hH2 : k1 + (1 - k1) * x - 3 * r / 2 = 0 := by
    calc k1 + (1 - k1) * x - 3 * r / 2 = (3 * r / 2) - 3 * r / 2 := by rw [hM_x]
      _ = 0 := by ring

  have hH4 : k2 + (1 - k2) * x - 3 * (1 - r) / 2 = 0 := by
    calc k2 + (1 - k2) * x - 3 * (1 - r) / 2 = (3 * (1 - r) / 2) - 3 * (1 - r) / 2 := by rw [hN_x]
      _ = 0 := by ring

  -- 4. Construct the polynomial linear combination that isolates r
  -- (This rigorous identity cleanly bypasses solving quadratics explicitly)
  have h_comb : 3 * r^2 - 1 =
      (r + 1) * (1 - x) * (k1 - (1 - r / 2))
    - (r + 1) * (k1 + (1 - k1) * x - 3 * r / 2)
    - r * (1 - x) * (k2 - (1 - r) / 2)
    + r * (k2 + (1 - k2) * x - 3 * (1 - r) / 2) := by ring

  -- 5. Substitute our zeroed equations into the combination
  have h_eq_zero : 3 * r^2 - 1 = 0 := by
    calc 3 * r^2 - 1 =
        (r + 1) * (1 - x) * (k1 - (1 - r / 2))
      - (r + 1) * (k1 + (1 - k1) * x - 3 * r / 2)
      - r * (1 - x) * (k2 - (1 - r) / 2)
      + r * (k2 + (1 - k2) * x - 3 * (1 - r) / 2) := h_comb
      _ = (r + 1) * (1 - x) * 0 - (r + 1) * 0 - r * (1 - x) * 0 + r * 0 := by rw [hH1, hH2, hH3, hH4]
      _ = 0 := by ring

  -- 6. Conclude the final value for r^2
  have h_3r2 : 3 * r^2 = 1 := by linarith [h_eq_zero]
  
  calc r^2 = (3 * r^2) / 3 := by ring
    _ = 1 / 3 := by rw [h_3r2]
