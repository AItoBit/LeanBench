/-- (a) Find all natural numbers `n` for which `7` divides `2 ^ n - 1`: the multiples of `3`.
(b) There is no positive natural number `n` for which `7` divides `2 ^ n + 1`. -/
theorem candidate :
    {n : ℕ | 7 ∣ (2 ^ n - 1 : ℕ)} = {n : ℕ | 3 ∣ n} ∧
      ¬∃ n, 0 < n ∧ 7 ∣ 2 ^ n + 1 :=
