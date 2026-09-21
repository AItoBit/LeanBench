open scoped Real

namespace IMO1991P6

/-- IMO 1991, Problem 6. -/

theorem candidate (a : ℝ) (ha : 1 < a) :
    ∃ x : ℕ → ℝ, (∃ C, ∀ i, |x i| ≤ C) ∧
      ∀ i j, i ≠ j → 1 ≤ |x i - x j| * |(i : ℤ) - j| ^ a :=
