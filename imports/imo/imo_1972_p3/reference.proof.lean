by
  obtain ⟨a, ha⟩ := key n m
  rw [← Int.natCast_dvd_natCast]
  refine ⟨a, ?_⟩
  have h : (((2 * m)! * (2 * n)! : ℕ) : ℚ)
      = ((m ! * n ! * (m + n)! : ℕ) : ℚ) * (a : ℚ) := by
    push_cast
    linear_combination ha
  exact_mod_cast h
