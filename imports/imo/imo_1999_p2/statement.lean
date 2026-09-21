/-- Part (b): for `C = 1 / 8`, equality holds exactly when two of the `x i` are equal to
each other and all the others are zero. -/
theorem candidate (hn : 2 ≤ n) (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∑ i, ∑ j ∈ Finset.Ioi i, x i * x j * (x i ^ 2 + x j ^ 2) = (1 / 8) * (∑ i, x i) ^ 4
      ↔ ∃ a b : Fin n, a ≠ b ∧ x a = x b ∧ ∀ k, k ≠ a → k ≠ b → x k = 0 :=
