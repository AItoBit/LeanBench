/-- Restatement: the set of real solutions of `P n (x) = x` has exactly `2 ^ n` elements. -/
theorem candidate (n : ℕ) (hn : 1 ≤ n) :
    {x : ℝ | (P n).eval x = x}.ncard = 2 ^ n :=
