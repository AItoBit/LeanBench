/-- **Part (b)**: the positive integers `m` attained by exactly one `k` are precisely the
numbers `n (n-1) / 2 + 1` for `n ≥ 2`. -/
theorem candidate (m : ℕ) (hm : 0 < m) :
    (∃! k : ℕ, 0 < k ∧ f k = m) ↔ ∃ n : ℕ, 2 ≤ n ∧ m = n * (n - 1) / 2 + 1 :=
