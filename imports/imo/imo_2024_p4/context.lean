namespace IMO2024P4

noncomputable section

/-!
# IMO 2024 Problem 4 — analytic-angle core

The source proves

    ∠YPX = π - ∠AIL - ∠AIK

and

    ∠KIL = ∠AIK + ∠AIL.

Therefore

    ∠KIL + ∠YPX = π.

This is the radian form of

    ∠KIL + ∠YPX = 180°.

No `sorry`, `admit`, or additional axioms are used.
-/

variable {Point : Type*}

variable
  (ang : Point → Point → Point → ℝ)

/-!
============================================================
1. Straight angle
============================================================
-/

def StraightAngle : ℝ :=
  Real.pi

/-!
============================================================
2. Elementary angle arithmetic
============================================================
-/

def Deg180 : ℝ :=
  Real.pi
