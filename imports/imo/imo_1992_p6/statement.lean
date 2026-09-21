/-- Merging `a` groups of four `1`s into `2`s and `b` groups of nine `1`s into `3`s turns the
representation `n² = 1² + ⋯ + 1²` into one with `n² - (3a + 8b)` positive squares. -/
theorem candidate (n a b : ℕ) (h : 4 * a + 9 * b ≤ n ^ 2) :
    Rep n (n ^ 2 - (3 * a + 8 * b)) :=
