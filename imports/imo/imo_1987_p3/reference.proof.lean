by

  -- Step 1: Establish S_ax^2 <= n * (k - 1)^2
  have h1 : S_ax^2 ≤ n * (k - 1)^2 := by
    calc S_ax^2 ≤ S_a * S_x := h_CS
      _ = S_a * 1 := by rw [h_Sx]
      _ = S_a := by ring
      _ ≤ n * (k - 1)^2 := h_Sa

  -- Step 2: Set up the bounding target and ensure non-negativity
  have hk_sub : 0 ≤ k - 1 := by linarith
  have hB_nonneg : 0 ≤ Real.sqrt n * (k - 1) := mul_nonneg (Real.sqrt_nonneg n) hk_sub

  -- Step 3: Expand the square of the target bound
  have hB_sq : (Real.sqrt n * (k - 1))^2 = n * (k - 1)^2 := by
    calc (Real.sqrt n * (k - 1))^2 = (Real.sqrt n)^2 * (k - 1)^2 := by ring
      _ = n * (k - 1)^2 := by rw [Real.sq_sqrt hn]

  -- Step 4: Relate the squared terms
  have h2 : S_ax^2 ≤ (Real.sqrt n * (k - 1))^2 := by
    calc S_ax^2 ≤ n * (k - 1)^2 := h1
      _ = (Real.sqrt n * (k - 1))^2 := hB_sq.symm

  -- Step 5: Extract the square root to finalize the deduction
  have h3 : Real.sqrt (S_ax^2) ≤ Real.sqrt ((Real.sqrt n * (k - 1))^2) := Real.sqrt_le_sqrt h2
  rw [Real.sqrt_sq h_Sax_nonneg, Real.sqrt_sq hB_nonneg] at h3

  exact h3
