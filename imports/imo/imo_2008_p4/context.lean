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
# IMO 2008, Problem 4

Find all functions `f : (0, ∞) → (0, ∞)` such that
`(f w ^ 2 + f x ^ 2) / (f (y ^ 2) + f (z ^ 2)) = (w ^ 2 + x ^ 2) / (y ^ 2 + z ^ 2)`
for all positive reals `w, x, y, z` with `w * x = y * z`.

The answer is `f x = x` for all `x > 0`, or `f x = 1 / x` for all `x > 0`.
-/

namespace Imo2008P4

/-- The functional equation, for a function `f : ℝ → ℝ` (only its values on the
positive reals are constrained). -/
def FE (f : ℝ → ℝ) : Prop :=
  ∀ w x y z : ℝ, 0 < w → 0 < x → 0 < y → 0 < z → w * x = y * z →
    (f w ^ 2 + f x ^ 2) / (f (y ^ 2) + f (z ^ 2)) = (w ^ 2 + x ^ 2) / (y ^ 2 + z ^ 2)
