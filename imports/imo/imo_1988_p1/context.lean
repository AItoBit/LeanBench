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
# IMO 1988 Problem 1

Consider two concentric circles with radii `R` and `r` (`R > r`) and centre `O`.
Fix `P` on the small circle and consider a variable chord `AP` of the small circle.
Points `B` and `C` lie on the large circle, `B`, `P`, `C` are collinear and `BC ⊥ AP`.

* (i)  For which values of `∠OPA` is `BC² + CA² + AB²` extremal?
       Answer: the quantity is **constant**, equal to `6R² + 2r²`, so it is extremal
       for every value of the angle.
* (ii) What are the possible positions of the midpoints `U` of `AB` and `V` of `AC`?
       Answer: they lie on the circle of radius `R/2` centred at the midpoint `M` of `OP`.
       In fact the locus is exactly that circle with its two points on the line `OP`
       removed: those two points would force the degenerate chord `A = P`.

Points are modelled as elements of the Euclidean plane `EuclideanSpace ℝ (Fin 2)`.
-/

namespace IMO1988Q1

open RealInnerProductSpace

/-- The Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-! ### Elementary two–dimensional facts -/

/-- The hypotheses of the problem, packaged for reuse. -/
structure Config (R r : ℝ) (O A P B C : Pt) : Prop where
  /-- `A` lies on the small circle. -/
  hA : dist A O = r
  /-- `P` lies on the small circle. -/
  hP : dist P O = r
  /-- `B` lies on the large circle. -/
  hB : dist B O = R
  /-- `C` lies on the large circle. -/
  hC : dist C O = R
  /-- `AP` is a genuine chord of the small circle. -/
  hAP : A ≠ P
  /-- `B` and `C` are distinct, so they span the line `BC`. -/
  hBC : B ≠ C
  /-- `B`, `P`, `C` are collinear. -/
  hcol : Collinear ℝ ({B, P, C} : Set Pt)
  /-- `BC` is perpendicular to `AP`. -/
  hperp : ⟪C - B, A - P⟫ = 0

namespace Config

variable {R r : ℝ} {O A P B C : Pt}

end Config

/-- Rotation by a right angle in the plane. -/
private noncomputable def rot (x : Pt) : Pt := !₂[-(x 1), x 0]
