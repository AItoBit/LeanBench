/-- The `3 * n` planes `x = k`, `y = k`, `z = k` for `k = 1, …, n` cover `gridS n`
and avoid the origin. -/
theorem candidate (n : ℕ) : CoversS n (3 * n) :=
