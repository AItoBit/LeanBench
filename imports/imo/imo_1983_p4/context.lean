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
# IMO 1983, Problem 4

Let `ABC` be an equilateral triangle and `E` the set of all points contained in the three
segments `AB`, `BC` and `CA` (including `A`, `B` and `C`).  For every partition of `E` into
two disjoint subsets, at least one of the two subsets contains the vertices of a
right-angled triangle.

The proof formalized here exhibits nine explicit points of `E` (three on each side) with the
property that any two-colouring of them produces a monochromatic right-angled triangle; the
relevant right angles are verified by computing inner products, and the colouring step is a
finite case check.
-/

namespace IMO1983Q4

open EuclideanGeometry RealInnerProductSpace

/-- The ambient Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- The set `E` of the statement: the union of the three closed sides of the triangle
`A B C`. -/
def sides (A B C : Pt) : Set Pt :=
  segment ℝ A B ∪ segment ℝ B C ∪ segment ℝ C A

/-- `S` contains the vertices of a (nondegenerate) right-angled triangle. -/
def HasRightTriangle (S : Set Pt) : Prop :=
  ∃ P ∈ S, ∃ Q ∈ S, ∃ R ∈ S,
    P ≠ Q ∧ R ≠ Q ∧ P ≠ R ∧ ¬ Collinear ℝ ({P, Q, R} : Set Pt) ∧ ∠ P Q R = π / 2

/-! ### Elementary geometric lemmas -/

variable {A B C : Pt}

/-- The point `A + a • (B - A) + b • (C - A)`. -/
noncomputable def upt (A B C : Pt) (a b : ℝ) : Pt := A + (a • (B - A) + b • (C - A))

section Equilateral

variable (hABBC : dist A B = dist B C) (hBCCA : dist B C = dist C A)

include hABBC hBCCA

variable (hAB : A ≠ B)

include hAB

end Equilateral

/-! ### Membership of the nine points in `E` -/

attribute [-instance] Classical.propDecidable in
