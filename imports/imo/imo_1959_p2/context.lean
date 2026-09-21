open Set Real

namespace Imo1959Q2

/-- The equation of the problem, together with the requirement that only non-negative reals
appear under the square roots. -/
def IsGood (x A : ℝ) : Prop :=
  √(x + √(2 * x - 1)) + √(x - √(2 * x - 1)) = A ∧ 0 ≤ 2 * x - 1 ∧
    0 ≤ x + √(2 * x - 1) ∧ 0 ≤ x - √(2 * x - 1)

variable {x A : ℝ}

end Imo1959Q2

open Imo1959Q2
