by
  rcases h_cons with ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩

  · -- Case 1: a = n, b = n+1, c = n+2
    rw [ha, hb, hc] at h_eq
    have h1 : n^2 + 5 * n + 3 = 0 := by
      calc n^2 + 5 * n + 3 = (n+1)*(n^2 + (n+2)^2 - (n+1)^2) - n^2*(n+2) := by ring
      _ = 0 := sub_eq_zero.mpr h_eq.symm
    have h2 : n * n + 5 * n + 3 = 0 := by
      calc n * n + 5 * n + 3 = n^2 + 5 * n + 3 := by ring
      _ = 0 := h1
    have h_nn : n * n > 0 := mul_pos h_pos h_pos
    linarith

  · -- Case 2: a = n, b = n+2, c = n+1
    rw [ha, hb, hc] at h_eq
    have h1 : n^2 + 7 * n + 6 = 0 := by
      calc n^2 + 7 * n + 6 = n^2*(n+1) - (n+2)*(n^2 + (n+1)^2 - (n+2)^2) := by ring
      _ = 0 := sub_eq_zero.mpr h_eq
    have h2 : n * n + 7 * n + 6 = 0 := by
      calc n * n + 7 * n + 6 = n^2 + 7 * n + 6 := by ring
      _ = 0 := h1
    have h_nn : n * n > 0 := mul_pos h_pos h_pos
    linarith

  · -- Case 3: a = n+1, b = n, c = n+2
    rw [ha, hb, hc] at h_eq h_tri
    have h1 : 2 * n^2 - 2 = 0 := by
      calc 2 * n^2 - 2 = n*((n+1)^2 + (n+2)^2 - n^2) - (n+1)^2*(n+2) := by ring
      _ = 0 := sub_eq_zero.mpr h_eq.symm
    have h2 : 2 * (n - 1) * (n + 1) = 0 := by
      calc 2 * (n - 1) * (n + 1) = 2 * n^2 - 2 := by ring
      _ = 0 := h1
    cases mul_eq_zero.mp h2 with
    | inl h3 =>
      cases mul_eq_zero.mp h3 with
      | inl h4 => revert h4; norm_num
      | inr h4 =>
        have : n > 1 := by linarith [h_tri.1]
        omega
    | inr h3 => omega

  · -- Case 4: a = n+1, b = n+2, c = n
    rw [ha, hb, hc] at h_eq
    have h1 : 2 * n^2 + 8 * n + 6 = 0 := by
      calc 2 * n^2 + 8 * n + 6 = (n+1)^2*n - (n+2)*((n+1)^2 + n^2 - (n+2)^2) := by ring
      _ = 0 := sub_eq_zero.mpr h_eq
    have h2 : 2 * (n + 1) * (n + 3) = 0 := by
      calc 2 * (n + 1) * (n + 3) = 2 * n^2 + 8 * n + 6 := by ring
      _ = 0 := h1
    cases mul_eq_zero.mp h2 with
    | inl h3 =>
      cases mul_eq_zero.mp h3 with
      | inl h4 => revert h4; norm_num
      | inr h4 => omega
    | inr h3 => omega

  · -- Case 5: a = n+2, b = n, c = n+1
    rw [ha, hb, hc] at h_eq
    have h1 : n^2 - 3 * n - 4 = 0 := by
      calc n^2 - 3 * n - 4 = n*((n+2)^2 + (n+1)^2 - n^2) - (n+2)^2*(n+1) := by ring
      _ = 0 := sub_eq_zero.mpr h_eq.symm
    have h2 : (n - 4) * (n + 1) = 0 := by
      calc (n - 4) * (n + 1) = n^2 - 3 * n - 4 := by ring
      _ = 0 := h1
    have hn4 : n = 4 := by
      cases mul_eq_zero.mp h2 with
      | inl h3 => omega
      | inr h3 => omega
    subst hn4
    subst ha hb hc
    decide

  · -- Case 6: a = n+2, b = n+1, c = n
    rw [ha, hb, hc] at h_eq h_tri
    have h1 : n^2 - n - 3 = 0 := by
      calc n^2 - n - 3 = (n+2)^2*n - (n+1)*((n+2)^2 + n^2 - (n+1)^2) := by ring
      _ = 0 := sub_eq_zero.mpr h_eq
    have _ht : n > 1 := by linarith [h_tri.2.1]
    have h_cases : n = 2 ∨ n ≥ 3 := by omega
    rcases h_cases with rfl | _hn3
    · revert h1; norm_num
    · have h_pos2 : (n - 3) * (n + 2) ≥ 0 := mul_nonneg (by omega) (by omega)
      have h_expand : (n - 3) * (n + 2) = n^2 - n - 6 := by ring
      linarith
