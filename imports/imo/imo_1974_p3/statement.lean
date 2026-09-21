/-- **IMO 1974, Problem 3.** For every `n ≥ 0` the number
`∑_{k=0}^{n} C(2n+1, 2k+1) * 2^(3k)` is not divisible by `5`. -/
theorem candidate (n : ℕ) :
    ¬ (5 ∣ ∑ k ∈ Finset.range (n + 1), (2 * n + 1).choose (2 * k + 1) * 2 ^ (3 * k)) :=
