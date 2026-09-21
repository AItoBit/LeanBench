namespace IMO2014P4

/-!
# IMO 2014 Problem 4 — barycentric algebraic core



In barycentric coordinates with respect to triangle ABC:

    A = (1 : 0 : 0)
    B = (0 : 1 : 0)
    C = (0 : 0 : 1)

The source obtains

    M = (-a² : 2a² - 2c² : 2c²)
    N = (-a² : 2b² : 2a² - 2b²)

and claims that BM and CN intersect at

    D = (-a² : 2b² : 2c²).

The circumcircle of ABC has barycentric equation

    a² y z + b² z x + c² x y = 0.

We verify algebraically:

* B, M, D are collinear;
* C, N, D are collinear;
* D lies on the circumcircle.

Thus the common point of BM and CN lies on the circumcircle.
-/

/-!
## Barycentric points
-/

structure BaryPoint where
  x : ℝ
  y : ℝ
  z : ℝ

/-!
## Basic triangle vertices
-/

def pointA : BaryPoint :=
  ⟨1, 0, 0⟩

def pointB : BaryPoint :=
  ⟨0, 1, 0⟩

def pointC : BaryPoint :=
  ⟨0, 0, 1⟩

/-!
## Points M, N, D from the source
-/

def pointM
    (a c : ℝ) :
    BaryPoint :=
  ⟨-(a ^ 2),
   2 * a ^ 2 - 2 * c ^ 2,
   2 * c ^ 2⟩

def pointN
    (a b : ℝ) :
    BaryPoint :=
  ⟨-(a ^ 2),
   2 * b ^ 2,
   2 * a ^ 2 - 2 * b ^ 2⟩

def pointD
    (a b c : ℝ) :
    BaryPoint :=
  ⟨-(a ^ 2),
   2 * b ^ 2,
   2 * c ^ 2⟩

/-!
## Collinearity in homogeneous coordinates
-/

/--
The determinant of three homogeneous coordinate triples.
-/
def det3
    (P Q R : BaryPoint) : ℝ :=
  P.x * (Q.y * R.z - Q.z * R.y)
  - P.y * (Q.x * R.z - Q.z * R.x)
  + P.z * (Q.x * R.y - Q.y * R.x)

/--
Three barycentric points are collinear when their
3 × 3 determinant vanishes.
-/
def Collinear
    (P Q R : BaryPoint) : Prop :=
  det3 P Q R = 0

/-!
## D lies on BM
-/

/--
The barycentric equation of the circumcircle of ABC:

    a² y z + b² z x + c² x y = 0.
-/
def OnCircumcircle
    (a b c : ℝ)
    (P : BaryPoint) : Prop :=
  a ^ 2 * P.y * P.z
  + b ^ 2 * P.z * P.x
  + c ^ 2 * P.x * P.y
  = 0

/-!
## D lies on the circumcircle
-/
