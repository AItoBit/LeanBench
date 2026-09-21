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

/-!
# IMO 1979 Problem 4

We consider a point `P` in a plane `p` and a point `Q ∉ p`.  Determine all points `R` of `p` for
which
$$\frac{QP + PR}{QR}$$
is maximum.

**Answer.** Let `T` be the orthogonal projection of `Q` on `p`.  The ratio is maximal exactly for
the points `R` of `p` lying on the ray `PT` with `PR = PQ`; that is, `R` is the intersection of the
ray `PT` with the sphere of centre `P` and radius `PQ`.  (If `PQ ⊥ p`, then `T = P`, the ray is
undefined and the maximum is attained at every point `R` of `p` with `PR = PQ`.)  The maximal value
of the ratio is `√(2·PQ / (PQ - PT))`.

Below the plane through `P` with (nonzero) normal vector `nv` is `Imo1979P4.plane P nv`, and `T` is
`Imo1979P4.foot P Q nv`.  The condition "`R` lies on the ray `PT`, this condition being vacuous
when `T = P`" is expressed as the equality case of the Cauchy–Schwarz inequality,
`⟪R - P, T - P⟫ = ‖R - P‖ * ‖T - P‖`.
-/

namespace Imo1979P4

open scoped RealInnerProductSpace

/-- The ambient Euclidean 3-space. -/
abbrev E : Type := EuclideanSpace ℝ (Fin 3)

/-- The plane through the point `P` with normal vector `nv`. -/
def plane (P nv : E) : Set E := {R : E | ⟪nv, R - P⟫ = 0}

/-- The orthogonal projection (the "foot") of the point `Q` on the plane
`Imo1979P4.plane P nv`. -/
noncomputable def foot (P Q nv : E) : E := Q - (⟪nv, Q - P⟫ / ‖nv‖ ^ 2) • nv

/-- The maximal value of `(QP + PR)/QR` for `R` in the plane through `P` with normal `nv`. -/
noncomputable def maxRatio (P Q nv : E) : ℝ :=
  Real.sqrt (2 * dist P Q / (dist P Q - dist P (foot P Q nv)))

section Basic

variable {P Q nv : E}

end Basic

section Main

variable {P Q nv : E}
