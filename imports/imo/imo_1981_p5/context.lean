open scoped BigOperators

open scoped Real

open scoped Nat

open scoped Classical

open scoped Pointwise

open RealInnerProductSpace

set_option maxHeartbeats 8000000

set_option maxRecDepth 4000

set_option synthInstance.maxHeartbeats 20000

set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false

set_option autoImplicit false

/-!
# IMO 1981, Problem 5

*Three congruent circles have a common point `O` and lie inside a given triangle.  Each circle
touches a pair of sides of the triangle.  Prove that the incenter and the circumcenter of the
triangle and the point `O` are collinear.*

The configuration is formalised in the Euclidean plane `EuclideanSpace ℝ (Fin 2)`:

* the triangle is given by three non-collinear points `A`, `B`, `C`;
* the three circles have a common radius `r` and centres `OA`, `OB`, `OC`, each of which lies
  inside the triangle (i.e. in the convex hull of `{A, B, C}`);
* the circle with centre `OA` is tangent to the lines `AB` and `AC`, the circle with centre `OB`
  is tangent to `AB` and `BC`, and the circle with centre `OC` is tangent to `AC` and `BC`;
* `O` lies on all three circles;
* `X` is a circumcenter of the triangle, i.e. a point equidistant from `A`, `B` and `C`.

One nondegeneracy assumption has to be added: the three circles must not all coincide.  (If the
common radius equals the inradius, then all three circles are the incircle, every point `O` of
the incircle satisfies the hypotheses, and the conclusion fails.)  We express this as
`OA ≠ OB`.

The conclusion is that the incenter, the circumcenter `X` and `O` are collinear.
-/

namespace IMO1981P5

/-- Points of the Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-! ### Elementary inner-product computations -/

/-- Twice the area of the triangle `A B C`, squared:
`gram A B C = ‖B - A‖² ‖C - A‖² - ⟪B - A, C - A⟫²`. -/
noncomputable def gram (A B C : Pt) : ℝ :=
  ‖B - A‖ ^ 2 * ‖C - A‖ ^ 2 - ⟪B - A, C - A⟫ ^ 2

/-- The circle with centre `P` and radius `r` is tangent to the line `AB`: the foot of the
perpendicular dropped from `P` to the line `AB` is at distance `r` from `P`. -/
def TangentToLine (P : Pt) (r : ℝ) (A B : Pt) : Prop :=
  ∃ s : ℝ, dist P (A + s • (B - A)) = r ∧ ⟪P - (A + s • (B - A)), B - A⟫ = 0

/-- The incenter of the triangle `A B C`, given by its barycentric coordinates
`(a : b : c)` where `a = |BC|`, `b = |CA|`, `c = |AB|`. -/
noncomputable def incenter (A B C : Pt) : Pt :=
  (dist B C / (dist B C + dist C A + dist A B)) • A +
  (dist C A / (dist B C + dist C A + dist A B)) • B +
  (dist A B / (dist B C + dist C A + dist A B)) • C

/-! ### The main theorem -/
