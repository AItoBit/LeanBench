/-- **IMO 2000, Problem 5.**  There exists a positive integer `n` with exactly `2000`
distinct prime divisors such that `n ∣ 2 ^ n + 1`. -/
theorem candidate :
    ∃ n : ℕ, 0 < n ∧ n.primeFactors.card = 2000 ∧ n ∣ 2 ^ n + 1 :=
