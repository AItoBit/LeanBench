/-- `a_{2n} = ((2 + √2)^(n-1) - (2 - √2)^(n-1)) / √2` for `n ≥ 1`. -/
theorem candidate (n : ℕ) (hn : 1 ≤ n) :
    (a (2 * n) : ℝ) =
      ((2 + Real.sqrt 2) ^ (n - 1) - (2 - Real.sqrt 2) ^ (n - 1)) / Real.sqrt 2 :=
