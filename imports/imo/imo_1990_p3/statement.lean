/-- **IMO 1990, Problem 3.** For an integer `n > 1`, `n ^ 2` divides `2 ^ n + 1`
if and only if `n = 3`. -/
theorem candidate (n : ℕ) (hn : 1 < n) : n ^ 2 ∣ 2 ^ n + 1 ↔ n = 3 :=
