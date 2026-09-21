/-- **IMO 1973, Problem 6.** -/
theorem candidate (n : ℕ) (hn : 0 < n) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (a : ℕ → ℝ) (ha : ∀ j, 0 < a j) :
    ∃ b : ℕ → ℝ,
      (∀ k, k < n → 0 < b k) ∧
      (∀ k, k < n → a k < b k) ∧
      (∀ k, k + 1 < n → q * b k < b (k + 1) ∧ q * b (k + 1) < b k) ∧
      (∑ k ∈ Finset.range n, b k) < (1 + q) / (1 - q) * ∑ k ∈ Finset.range n, a k :=
