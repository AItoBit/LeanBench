by
  have hsets : {a : ℤ | 0 < a ∧ ∃ z : ℤ,
      ((a : ℚ) ^ m + a - 1) / ((a : ℚ) ^ n + a ^ 2 - 1) = z} =
      {a : ℤ | 0 < a ∧ a ^ n + a ^ 2 - 1 ∣ a ^ m + a - 1} := by
    ext a
    simp only [Set.mem_ofPred_eq]
    by_cases ha : 0 < a
    · simp only [ha, true_and, quotient_integer_iff_dvd ha]
    · simp only [ha, false_and]
  rw [hsets]
  exact result hm hn
