namespace IMO2016P1

/-!
# IMO 2016 Problem 1 — symmetry/concurrency core

The source eventually proves:

* `B` and `X` are symmetric with respect to `ME`;
* `D` and `F` are symmetric with respect to `ME`.

Thus reflection in `ME` sends line `BD` to line `FX`.

We choose coordinates so that `ME` is the y-axis.

No `sorry`, `admit`, or additional axioms are used.
-/

abbrev Point := ℝ × ℝ

/-!
## Reflection
-/

/--
Reflection in the y-axis.
-/
def reflectAxis (P : Point) : Point :=
  (-P.1, P.2)

/--
A point lies on the symmetry axis.
-/
def OnAxis (P : Point) : Prop :=
  P.1 = 0

/-!
## Collinearity
-/

/--
Three points are collinear when their determinant vanishes.
-/
def Collinear
    (P Q R : Point) : Prop :=
  (Q.1 - P.1) * (R.2 - P.2) -
    (Q.2 - P.2) * (R.1 - P.1) = 0

/-!
## Affine points on a line
-/

def affinePoint
    (P Q : Point)
    (t : ℝ) : Point :=
  ((1 - t) * P.1 + t * Q.1,
   (1 - t) * P.2 + t * Q.2)

/--
Explicit parameter used to intersect `BD` with the y-axis.
-/
noncomputable def axisParameter
    (B D : Point) : ℝ :=
  B.1 / (B.1 - D.1)

/--
Explicit point on `BD` used in the construction.
-/
noncomputable def axisIntersection
    (B D : Point) : Point :=
  affinePoint B D (axisParameter B D)
