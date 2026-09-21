open scoped BigOperators

open scoped Real

open scoped Nat

open scoped Classical

open scoped Pointwise

open scoped RealInnerProductSpace

set_option maxHeartbeats 8000000

set_option maxRecDepth 4000

set_option synthInstance.maxHeartbeats 20000

set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false

set_option autoImplicit false

set_option grind.warning false

/-!
# IMO 1966, Problem 3

Prove that the sum of the distances of the vertices of a regular tetrahedron from the
center of its circumscribed sphere is less than the sum of the distances of these
vertices from any other point in space.
-/

namespace IMO1966Q3

/-- Euclidean 3-space, the ambient space of the problem. -/
abbrev E := EuclideanSpace ℝ (Fin 3)
