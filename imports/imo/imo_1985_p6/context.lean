open Set

namespace Imo1985P6

/-- `s t k` is `x_{k+1}` when `x₁ = t`. -/
noncomputable def s (t : ℝ) : ℕ → ℝ
  | 0 => t
  | k + 1 => s t k * (s t k + 1 / ((k : ℝ) + 1))

/-- Good parameters: every term lies strictly inside its window. -/
abbrev Good (t : ℝ) : Prop := ∀ k : ℕ, 1 - 1 / ((k : ℝ) + 1) < s t k ∧ s t k < 1

/-- Parameters whose first `n + 1` terms lie in the closed windows. -/
def K (n : ℕ) : Set ℝ :=
  ⋂ m, ⋂ (_ : m ≤ n), {t | 1 - 1 / ((m : ℝ) + 1) ≤ s t m ∧ s t m ≤ 1}
