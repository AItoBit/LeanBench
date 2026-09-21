/-- Exactly the odd natural numbers occur as integer divisor-count ratios. -/
theorem candidate (k : ℕ) :
    (∃ n : ℕ, 0 < n ∧
      (d (n ^ 2) : ℚ) / d n = (k : ℚ)) ↔ Odd k :=
