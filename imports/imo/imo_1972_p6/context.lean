open scoped BigOperators

open scoped Real

open scoped Nat

open scoped Classical

open scoped Pointwise

open scoped InnerProductSpace

set_option maxHeartbeats 8000000

set_option maxRecDepth 4000

set_option synthInstance.maxHeartbeats 20000

set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false

set_option autoImplicit false

set_option grind.warning false

/-!
# IMO 1972 Problem 6

*Given four distinct parallel planes, prove that there exists a regular tetrahedron with a
vertex on each plane.*

We model three-dimensional Euclidean space by `EuclideanSpace ℝ (Fin 3)`.  A family of four
parallel planes with common (nonzero) normal vector `n` is the family `{x | ⟪x, n⟫ = c i}`
for `i : Fin 4`; the planes are pairwise distinct exactly when `c` is injective.  A *regular
tetrahedron* is a family of four points whose pairwise distances are all equal to one and the
same positive number.

The construction: start from the reference regular tetrahedron `T` whose vertices are four
alternating vertices of a cube.  Its orthogonal projections onto a direction `w` are the four
numbers `⟪T i, w⟫`, and by solving a small linear system one can choose `w` so that these are
any four prescribed numbers of sum zero.  Rotating `w / ‖w‖` onto the unit normal `n / ‖n‖`
and scaling by `‖w‖` then places the four vertices on the four given planes.
-/

namespace IMO1972P6

/-- Three-dimensional Euclidean space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The vertices of a reference regular tetrahedron: four alternating vertices of a cube. -/
def T : Fin 4 → E3 := ![!₂[1, 1, 1], !₂[1, -1, -1], !₂[-1, 1, -1], !₂[-1, -1, 1]]
