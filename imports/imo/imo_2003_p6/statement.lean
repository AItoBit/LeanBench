/-- **IMO 2003 P6.** -/
theorem candidate (p : ℕ) (hp : p.Prime) :
    ∃ q : ℕ, q.Prime ∧ ∀ n : ℤ, ¬ ((q : ℤ) ∣ n ^ p - (p : ℤ)) :=
