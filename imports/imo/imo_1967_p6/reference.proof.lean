by
  -- Retrieve the explicit formula evaluated at k = n - 1
  have h_expl := m_explicit m_seq m h0 h_rec (n - 1)
  rw [h_end] at h_expl

  -- Robust casting for (n - 1 : ℝ) given that 0 < n
  have hn_cast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have h_eq : n - 1 + 1 = n := Nat.sub_add_cancel hn
    have h_cast : ((n - 1 + 1 : ℕ) : ℝ) = (n : ℝ) := by rw [h_eq]
    push_cast at h_cast
    linarith

  rw [hn_cast] at h_expl

  -- Isolate the term containing (m - 36)
  have h2 : 7 * ((n : ℝ) - 6) = (m - 36) * (6 / 7) ^ (n - 1) := by
    calc 7 * ((n : ℝ) - 6) = (n : ℝ) + 6 * ((n : ℝ) - 1) - 36 := by ring
    _ = (m - 36) * (6 / 7) ^ (n - 1) := by linarith [h_expl]

  -- Show that multiplying the reciprocal powers cancels out to 1
  have h4 : (6 / 7 : ℝ) ^ (n - 1) * (7 / 6) ^ (n - 1) = 1 := by
    rw [← mul_pow]
    have h_mul : (6 / 7 : ℝ) * (7 / 6) = 1 := by norm_num
    rw [h_mul, one_pow]

  -- Final rearrangement to reach the target identity
  calc m - 36 = (m - 36) * 1 := by ring
    _ = (m - 36) * ((6 / 7) ^ (n - 1) * (7 / 6) ^ (n - 1)) := by rw [h4]
    _ = (m - 36) * (6 / 7) ^ (n - 1) * (7 / 6) ^ (n - 1) := by ring
    _ = 7 * ((n : ℝ) - 6) * (7 / 6) ^ (n - 1) := by rw [← h2]
