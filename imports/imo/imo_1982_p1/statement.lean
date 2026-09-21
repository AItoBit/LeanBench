namespace Imo1982P1

/-- **IMO 1982, Problem 1.** -/

theorem candidate (f : ℕ → ℕ)
    (h : ∀ m n, 1 ≤ m → 1 ≤ n → f (m + n) = f m + f n ∨ f (m + n) = f m + f n + 1)
    (h2 : f 2 = 0) (h3 : 0 < f 3) (h9999 : f 9999 = 3333) :
    f 1982 = 660 :=
