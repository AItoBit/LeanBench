/-- **IMO 1983, Problem 3.**  For positive integers `a`, `b`, `c` that are pairwise coprime,
`2abc - ab - bc - ca` is the largest integer that cannot be written as `x*bc + y*ca + z*ab`
with `x, y, z` non-negative integers. -/
theorem candidate (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b) (hbc : Nat.Coprime b c) (hca : Nat.Coprime c a) :
    IsGreatest {n : ℤ | ¬ ∃ x y z : ℕ, n = x * (b * c) + y * (c * a) + z * (a * b)}
      (2 * a * b * c - a * b - b * c - c * a) :=
