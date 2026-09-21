/-- IMO 2003, Problem 5, with the corrected coefficient for unordered pairs.
The indices are 0-based. The sums include each pair i < j once; adding the
zero diagonal terms gives the equivalent convention i ≤ j.
The second conjunct proves equality if and only if the sequence is arithmetic. -/
theorem candidate (n : ℕ) (hn : 0 < n) (x : ℕ → ℝ)
    (hx : ∀ i j, i ≤ j → j < n → x i ≤ x j) :
    spread n x ^ 2 ≤ (((n : ℝ) ^ 2 - 1) / 3) * energy n x ∧
    (spread n x ^ 2 = (((n : ℝ) ^ 2 - 1) / 3) * energy n x ↔ IsArithmetic n x) :=
