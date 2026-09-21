/-- **IMO 2004 P6, the "only if" direction.** -/
theorem candidate (n : ℕ) (h : 20 ∣ n) :
    ¬ ∃ m : ℕ, 0 < m ∧ n ∣ m ∧ Alternating m :=
