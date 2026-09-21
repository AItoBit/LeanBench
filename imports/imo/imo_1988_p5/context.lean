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
# IMO 1988, Problem 5

In a right-angled triangle `ABC` (with the right angle at `A`) let `AD` be the altitude drawn to
the hypotenuse `BC`, and let the straight line joining the incentres of the triangles `ABD`, `ACD`
intersect the sides `AB`, `AC` at the points `K`, `L` respectively.  If `E` and `E₁` denote the
areas of the triangles `ABC` and `AKL` respectively, then `E / E₁ ≥ 2`.

The proof shows that `AK = AL = AD`, which gives `E / E₁ = BC ^ 2 / (AB * AC) ≥ 2`.
-/

open EuclideanGeometry

open scoped RealInnerProductSpace

namespace Imo1988P5

/-- The plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- The area of the triangle with vertices `X`, `Y`, `Z`, computed as half the product of the
two sides at `X` with the sine of the angle at `X`. -/
noncomputable def area (X Y Z : Pt) : ℝ :=
  1 / 2 * dist X Y * dist X Z * Real.sin (∠ Y X Z)
