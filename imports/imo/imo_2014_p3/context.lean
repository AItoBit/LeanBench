namespace IMO2014P3

/-!
IMO 2014 Problem 3 — final geometric core.

The source proves that the circumcenter `G` of triangle `TSH`
lies on the altitude `AH`.

Since `H` is the foot of the perpendicular from `A` to `BD`,

    AH ⟂ BD.

Since `G` lies on `AH`, the radius `GH` is also perpendicular
to `BD`. Therefore `BD` is tangent to the circumcircle of
`TSH` at `H`.

No `sorry`, `admit`, or extra axioms.
-/

abbrev Point := ℝ × ℝ

/-!
## Basic coordinate geometry
-/

def vec (P Q : Point) : Point :=
  (Q.1 - P.1, Q.2 - P.2)

def dot (u v : Point) : ℝ :=
  u.1 * v.1 + u.2 * v.2

def distSq (P Q : Point) : ℝ :=
  (Q.1 - P.1) ^ 2 +
  (Q.2 - P.2) ^ 2

def Perpendicular
    (P Q R S : Point) : Prop :=
  dot (vec P Q) (vec R S) = 0

def Collinear
    (P Q R : Point) : Prop :=
  (Q.1 - P.1) * (R.2 - P.2) -
    (Q.2 - P.2) * (R.1 - P.1) = 0

/-!
## Circle data
-/

/--
`O` is the circumcenter of `P,Q,R`.
-/
def IsCircumcenter
    (O P Q R : Point) : Prop :=
  distSq O P = distSq O Q ∧
  distSq O Q = distSq O R

/--
Analytic tangency criterion:
the radius through the touching point is perpendicular
to the tangent line.
-/
def TangentAt
    (O H B D : Point) : Prop :=
  Perpendicular O H B D

/-!
## Point lying on AH
-/

/--
`G` lies on the line through `H` and `A`.

We encode this by saying that vector `HG`
is a scalar multiple of vector `HA`.
-/
def LiesOnHA
    (A H G : Point) : Prop :=
  ∃ c : ℝ,
    G.1 - H.1 =
      c * (A.1 - H.1) ∧
    G.2 - H.2 =
      c * (A.2 - H.2)

/-!
## Main perpendicularity lemma
-/
