/-- **IMO 2004 P4.** -/
theorem candidate (n : ℕ) (hn : 3 ≤ n) (t : Fin n → ℝ) (ht : ∀ i, 0 < t i)
    (hsum : (∑ i, t i) * (∑ i, 1 / t i) < (n : ℝ) ^ 2 + 1)
    (i j k : Fin n) (hij : i < j) (hjk : j < k) :
    t k < t i + t j ∧ t i < t j + t k ∧ t j < t i + t k :=
