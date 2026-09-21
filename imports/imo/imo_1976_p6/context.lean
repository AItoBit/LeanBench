open scoped BigOperators

open scoped Real

open scoped Nat

open scoped Classical

open scoped Pointwise

set_option maxHeartbeats 8000000

set_option maxRecDepth 4000

set_option relaxedAutoImplicit false

set_option autoImplicit false

set_option grind.warning false

namespace Imo1976P6

/-- The sequence `u₀ = 2`, `u₁ = 5/2`, `u_{n+1} = u_n (u_{n-1}² - 2) - u₁`. -/
noncomputable def u : ℕ → ℝ
  | 0 => 2
  | 1 => 5 / 2
  | (n + 2) => u (n + 1) * ((u n) ^ 2 - 2) - 5 / 2

/-- The exponent sequence `eₙ = (2ⁿ - (-1)ⁿ)/3`, defined by the recursion
`e₀ = 0`, `e₁ = 1`, `e_{n+2} = e_{n+1} + 2 eₙ`. -/
def expo : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | (n + 2) => expo (n + 1) + 2 * expo n
