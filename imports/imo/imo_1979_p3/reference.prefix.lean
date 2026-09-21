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

/-- Both moving points start at `A`. -/
theorem imo1979P3Motion_zero (O A : ℂ) : imo1979P3Motion O A 0 = A := by
  simp [imo1979P3Motion]

/-- Both moving points are back at `A` after one revolution. -/
theorem imo1979P3Motion_one (O A : ℂ) : imo1979P3Motion O A 1 = A := by
  simp [imo1979P3Motion, Complex.exp_two_pi_mul_I]

/-- A moving point indeed travels on the circle centred at `O` through `A`. -/
theorem dist_imo1979P3Motion_center (O A : ℂ) (t : ℝ) :
    dist (imo1979P3Motion O A t) O = dist A O := by
  rw [Complex.dist_eq, Complex.dist_eq, imo1979P3Motion]
  have h0 : O + (A - O) * Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I) - O
      = (A - O) * Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I) := by ring
  rw [h0, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- The purely algebraic identity underlying the solution. -/
private theorem key_identity (r₁ s₁ r₂ s₂ x y u v N : ℂ) (hu : u * v = 1)
    (hx : x * (s₁ - s₂) = N) (hy : y * (r₁ - r₂) = N) (hN : N = r₂ * s₂ - r₁ * s₁) :
    (r₁ * (u - 1) - x) * (s₁ * (v - 1) - y) = (r₂ * (u - 1) - x) * (s₂ * (v - 1) - y) := by
  linear_combination (r₁ * s₁ - r₂ * s₂) * hu + (1 - v) * hx + (1 - u) * hy +
    (2 - u - v) * hN
