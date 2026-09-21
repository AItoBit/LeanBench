open scoped BigOperators

open scoped Real

open scoped Nat

open scoped Classical

open scoped Pointwise

set_option maxHeartbeats 8000000

set_option maxRecDepth 4000

set_option synthInstance.maxHeartbeats 20000

set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false

set_option autoImplicit false

set_option grind.warning false

/-- The leading coefficient of the quadratic in `cos (2 * x)`. -/
def imo1959P3F₀ (a _b _c : ℝ) : ℝ := a ^ 2

/-- The linear coefficient of the quadratic in `cos (2 * x)`. -/
def imo1959P3F₁ (a b c : ℝ) : ℝ := 2 * a ^ 2 + 4 * a * c - 2 * b ^ 2

/-- The constant coefficient of the quadratic in `cos (2 * x)`. -/
def imo1959P3F₂ (a b c : ℝ) : ℝ := a ^ 2 + 4 * a * c + 4 * c ^ 2 - 2 * b ^ 2

-- note: https://artofproblemsolving.com/community/c6h54819p27098808  suggests that the question should be "whose roots include" rather than "whose roots are the same as", otherwise $a = b = 1, c = 0$ is a counterexample. As a result we use `→` not `↔`.
