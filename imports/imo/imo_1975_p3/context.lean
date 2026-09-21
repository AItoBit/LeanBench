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
# IMO 1975, Problem 3

On the sides of an arbitrary triangle `ABC`, triangles `ABR`, `BCP`, `CAQ` are constructed
externally with `∠CBP = ∠CAQ = 45°`, `∠BCP = ∠ACQ = 30°`, `∠ABR = ∠BAR = 15°`.
Prove that `∠QRP = 90°` and `QR = RP`.

The plane is modelled as `ℂ`.  Directed angles are used, which encodes at the same time the
size of each of the given angles and the fact that the auxiliary triangles are erected on the
outside of `ABC`; the triangle `ABC` is assumed to be positively oriented, which is the
hypothesis `horient` below (it also encodes the nondegeneracy of the triangle `ABC`).  The
statement that the ray from `X` towards `Z` is obtained from the ray from `X` towards `Y` by
the rotation through the angle `θ` is written as `∃ t : ℝ, 0 < t ∧ Z - X = t * rot θ * (Y - X)`,
where `rot θ` denotes the rotation by `θ`.
-/

namespace IMO1975Q3

open Complex Real

/-- Multiplication by `rot θ` is the counterclockwise rotation of the plane `ℂ` by `θ`. -/
noncomputable def rot (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

/-- The coefficient of the apex `P`:  `P = B + pC * (C - B)`. -/
noncomputable def pC : ℂ := (((Real.sqrt 3 - 1) / 2 : ℝ) : ℂ) * (1 - Complex.I)

/-- The coefficient of the apex `Q`:  `Q = C + qC * (A - C)`. -/
noncomputable def qC : ℂ :=
  ((Real.sqrt 3 - 1 : ℝ) : ℂ) * (((Real.sqrt 3 : ℝ) : ℂ) - Complex.I) / 2

/-- The coefficient of the apex `R`:  `R = A + rC * (B - A)`. -/
noncomputable def rC : ℂ := (1 + ((Real.sqrt 3 - 2 : ℝ) : ℂ) * Complex.I) / 2
