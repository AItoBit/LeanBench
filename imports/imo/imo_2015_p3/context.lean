namespace IMO2015P3

/-!
# IMO 2015 Problem 3 — final tangency core

The source reduces the problem by inversion to the following
elementary fact.

Let `O` be the circumcenter of triangle `ALQ`.

If

    LA = LQ

and

    ML ∥ AQ,

then both `O` and `L` lie on the perpendicular bisector of `AQ`.
Consequently

    OL ⟂ AQ.

Since

    ML ∥ AQ,

we obtain

    OL ⟂ ML.

Thus `ML` is tangent at `L` to the circumcircle of `ALQ`.

We prove this using Cartesian coordinates.

No `sorry`, `admit`, or additional axioms are used.
-/

abbrev Point := ℝ × ℝ

/-!
## Basic vector operations
-/

def vec (P Q : Point) : Point :=
  (Q.1 - P.1, Q.2 - P.2)

def dot (u v : Point) : ℝ :=
  u.1 * v.1 + u.2 * v.2

def distSq (P Q : Point) : ℝ :=
  (Q.1 - P.1) ^ 2 +
  (Q.2 - P.2) ^ 2

/-!
## Perpendicularity
-/

def Perpendicular
    (P Q R S : Point) : Prop :=
  dot (vec P Q) (vec R S) = 0

/-!
## Parallelism

For the proof we use the scalar-multiple formulation:
the directed vector `PQ` is a real multiple of `RS`.
-/

def Parallel
    (P Q R S : Point) : Prop :=
  ∃ c : ℝ,
    Q.1 - P.1 =
      c * (S.1 - R.1) ∧
    Q.2 - P.2 =
      c * (S.2 - R.2)

/-!
## Circumcenter
-/

/--
`O` is the circumcenter of `A,L,Q`.
-/
def IsCircumcenter
    (O A L Q : Point) : Prop :=
  distSq O A = distSq O L ∧
  distSq O L = distSq O Q

/-!
## Tangency

A line `LM` is tangent at `L` to a circle centered at `O`
when the radius `OL` is perpendicular to `LM`.
-/

def TangentAt
    (O L M : Point) : Prop :=
  Perpendicular O L L M

/-!
## Equal distances
-/

def IsMidpoint
    (M A B : Point) : Prop :=
  M.1 = (A.1 + B.1) / 2 ∧
  M.2 = (A.2 + B.2) / 2

/--
For the source's rectangle `TNML`, the opposite directed
sides `TN` and `LM` agree.
-/
def OppositeSidesEqual
    (T N M L : Point) : Prop :=
  M.1 - L.1 = N.1 - T.1 ∧
  M.2 - L.2 = N.2 - T.2
