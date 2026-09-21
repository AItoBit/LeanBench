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
# IMO 1974, Problem 2

In the triangle `ABC`, prove that there is a point `D` on side `AB` such that `CD` is the
geometric mean of `AD` and `DB` if and only if `sin A * sin B ≤ sin (C / 2) ^ 2`.
-/

namespace IMO1974P2

open EuclideanGeometry Real

open scoped RealInnerProductSpace

/-- The plane in which the triangle lives. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)
