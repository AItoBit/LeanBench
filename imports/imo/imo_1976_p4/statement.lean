/-- The greatest product of positive integers with sum `1976` is `2 * 3 ^ 658`. -/
theorem candidate :
    IsGreatest {p : ℕ | ∃ l : List ℕ, (∀ x ∈ l, 0 < x) ∧ l.sum = 1976 ∧ l.prod = p}
      (2 * 3 ^ 658) :=
