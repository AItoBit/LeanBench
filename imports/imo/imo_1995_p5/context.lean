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
# IMO 1995, Problem 5

Let `ABCDEF` be a convex hexagon with `AB = BC = CD` and `DE = EF = FA`, such that
`∠BCD = ∠EFA = π/3`.  Suppose `G` and `H` are points in the interior of the hexagon such
that `∠AGB = ∠DHE = 2π/3`.  Prove that `AG + GB + GH + DH + HE ≥ CF`.

The plane is modelled by `ℂ`, distances are the usual `dist`, and angles are
`EuclideanGeometry.angle`.

The proof follows the classical solution.  The hypotheses `AB = BC = CD` and `∠BCD = π/3`
force the triangle `BCD` to be equilateral, and similarly for `EFA`; moreover `B` and `E`
are then both equidistant from `A` and `D`, so that `BE` is the perpendicular bisector
of `AD`.  Erecting equilateral triangles `AIB` and `DJE` outwards, Ptolemy's inequality
gives `GI ≤ GA + GB` and `HJ ≤ HD + HE`, while the perpendicularity gives `IJ = CF`; the
triangle inequality `IJ ≤ IG + GH + HJ` finishes the proof.
-/

namespace IMO1995P5

/-- The rotation by `-π/3`, as a complex number of modulus one. -/
noncomputable def wb : ℂ := ⟨1 / 2, -Real.sqrt 3 / 2⟩

/-- `ccw p q r` says that the triple `(p, q, r)` makes a strict left turn, i.e. `r` lies
strictly to the left of the directed line from `p` to `q`. -/
def ccw (p q r : ℂ) : Prop := 0 < ((starRingEnd ℂ) (q - p) * (r - p)).im

/-- A hexagon `ABCDEF` traversed counterclockwise, all of whose vertices are strictly
convex. -/
def CCWHexagon (A B C D E F : ℂ) : Prop :=
  ccw A B C ∧ ccw B C D ∧ ccw C D E ∧ ccw D E F ∧ ccw E F A ∧ ccw F A B

/-- `ABCDEF` is a convex hexagon: traversing its vertices in the given order (or in the
reversed order), every vertex is a strict turn in the same direction. -/
def ConvexHexagon (A B C D E F : ℂ) : Prop :=
  CCWHexagon A B C D E F ∨ CCWHexagon F E D C B A
