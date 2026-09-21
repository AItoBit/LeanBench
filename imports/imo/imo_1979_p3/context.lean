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
# IMO 1979, Problem 3

*Two circles in a plane intersect. `A` is one of the points of intersection. Starting
simultaneously from `A` two points move with constant speed, each travelling along its own circle
in the same sense. The two points return to `A` simultaneously after one revolution. Prove that
there is a fixed point `P` in the plane such that the two points are always equidistant from `P`.*

The plane is modelled as `ℂ`. A circle through `A` with centre `O` is the circle of radius
`‖A - O‖` about `O`; a point that starts at `A` at time `t = 0`, travels with constant speed in
the positive sense and completes one revolution in one unit of time is then

`imo1979P3Motion O A t = O + (A - O) * exp (2 * π * t * I)`.

Two *distinct* circles that meet at a common point `A` necessarily have distinct centres, which is
the hypothesis `O₁ ≠ O₂`.

The required fixed point is `imo1979P3Point O₁ O₂ A`.
-/

namespace Imo1979P3

open Complex

/-- The position at time `t` of a point that starts at `A`, moves along the circle with centre `O`
through `A` in the positive sense with constant speed, and makes exactly one revolution per unit of
time. -/
noncomputable def imo1979P3Motion (O A : ℂ) (t : ℝ) : ℂ :=
  O + (A - O) * Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)

/-- The fixed point equidistant from the two moving points, for the two circles with centres
`O₁ ≠ O₂` meeting at `A`. -/
noncomputable def imo1979P3Point (O₁ O₂ A : ℂ) : ℂ :=
  A + ((Complex.normSq (A - O₂) - Complex.normSq (A - O₁) : ℝ) : ℂ) /
      (starRingEnd ℂ) (O₂ - O₁)
