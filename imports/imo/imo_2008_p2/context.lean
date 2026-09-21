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

set_option pp.fullNames true

set_option pp.structureInstances true

set_option pp.coercions.types true

set_option pp.funBinderTypes true

set_option pp.letVarTypes true

set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# IMO 2008 Problem 2

**(i)** If `x, y, z` are three real numbers, all different from `1`, such that `x * y * z = 1`,
then `x²/(x-1)² + y²/(y-1)² + z²/(z-1)² ≥ 1`.

**(ii)** Equality is achieved for infinitely many triples of rational numbers `x, y, z`
(all different from `1`, with `x * y * z = 1`).
-/

namespace Imo2008P2

/-- The rational family achieving equality, parametrized by `k : ℚ` with `k ≠ ±1`. -/
def tripleOf (k : ℚ) : ℚ × ℚ × ℚ :=
  ((1 - k ^ 2) / 4, -2 * (k + 1) / (k - 1) ^ 2, 2 * (k - 1) / (k + 1) ^ 2)

/-- The set of rational triples `(x, y, z)`, all entries different from `1`, with `x * y * z = 1`
and with equality `x²/(x-1)² + y²/(y-1)² + z²/(z-1)² = 1`. -/
def equalitySet : Set (ℚ × ℚ × ℚ) :=
  {p : ℚ × ℚ × ℚ | p.1 ≠ 1 ∧ p.2.1 ≠ 1 ∧ p.2.2 ≠ 1 ∧ p.1 * p.2.1 * p.2.2 = 1 ∧
    p.1 ^ 2 / (p.1 - 1) ^ 2 + p.2.1 ^ 2 / (p.2.1 - 1) ^ 2 + p.2.2 ^ 2 / (p.2.2 - 1) ^ 2 = 1}
