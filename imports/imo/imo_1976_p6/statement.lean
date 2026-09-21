/-- **IMO 1976, Problem 6.** For `n ≥ 1`, `⌊uₙ⌋ = 2^{(2ⁿ - (-1)ⁿ)/3}`, where the exponent
`m` is characterized by `3 m = 2ⁿ - (-1)ⁿ`. -/
theorem candidate (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (hm : 3 * (m : ℤ) = 2 ^ n - (-1) ^ n) :
    ⌊u n⌋ = 2 ^ m :=
