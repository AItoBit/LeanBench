namespace Imo1977P6

/-- **IMO 1977, Problem 6.** -/

theorem candidate (f : ℕ → ℕ) (hpos : ∀ n, 0 < n → 0 < f n)
    (h : ∀ n, 0 < n → f (n + 1) > f (f n)) :
    ∀ n, 0 < n → f n = n :=
