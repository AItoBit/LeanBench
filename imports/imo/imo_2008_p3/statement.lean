/-- **IMO 2008 P3.** -/
theorem candidate :
    {n : ℕ | 0 < n ∧ ∃ p : ℕ, p.Prime ∧ p ∣ n ^ 2 + 1 ∧
      (2 * (n : ℝ) + Real.sqrt (2 * (n : ℝ)) < p)}.Infinite :=
