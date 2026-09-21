/-- **IMO 1996 P6.** -/
theorem candidate (p q n : ℕ) (hp : 0 < p) (hq : 0 < q) (hpq : p + q < n)
    (x : ℕ → ℤ) (h0 : x 0 = 0) (hn : x n = 0)
    (hstep : ∀ i, i < n → x (i + 1) - x i = (p : ℤ) ∨ x (i + 1) - x i = -(q : ℤ)) :
    ∃ i j, i < j ∧ j ≤ n ∧ ¬(i = 0 ∧ j = n) ∧ x i = x j :=
