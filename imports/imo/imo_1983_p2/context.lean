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
# IMO 1983, Problem 2

Let `A` be one of the two distinct points of intersection of two unequal coplanar circles
`C₁` and `C₂` with centres `O₁` and `O₂` respectively.  One of the common tangents to the
circles touches `C₁` at `P₁` and `C₂` at `P₂`, while the other touches `C₁` at `Q₁` and `C₂`
at `Q₂`.  Let `M₁` be the midpoint of `P₁Q₁` and `M₂` the midpoint of `P₂Q₂`.
Prove that `∠O₁AO₂ = ∠M₁AM₂`.

The plane is modelled by `EuclideanSpace ℝ (Fin 2)`.  A line through two distinct points `S`
and `T` is tangent to a circle with centre `O` and radius `r` at a point `Z` of the circle
exactly when `Z` lies on the circle and `OZ` is perpendicular to the direction of the line;
this is how the tangency hypotheses are phrased below.
-/

namespace IMO1983Q2

/-- The Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- A point of the plane given by its two coordinates. -/
noncomputable def mkP (a b : ℝ) : Plane := !₂[a, b]
