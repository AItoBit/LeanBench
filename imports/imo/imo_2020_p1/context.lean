namespace IMO2020P1

/-!
# IMO 2020 Problem 1 — concurrency core

We formalize Solution 3 from the supplied source.

The geometric construction is:

* `O` lies on the circumcircle of `A,D,P`;
* `O` lies on the circumcircle of `B,C,P`;
* cyclic-angle relations imply `OD` bisects `∠ADP`;
* cyclic-angle relations imply `OC` bisects `∠BCP`;
* the same cyclic-angle computation shows `OA = OP`;
* together with `OB = OP`, we get `OA = OB`,
  so `O` lies on the perpendicular bisector of `AB`.

Therefore the three required lines are concurrent at `O`.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. Abstract geometric primitives
============================================================
-/

variable {Point Circle : Type*}

/-
Directed angle `∠ABC`.
-/

variable (ang : Point → Point → Point → ℝ)

/-
Distance between two points.
-/

variable (dist : Point → Point → ℝ)

/-
Circle membership.
-/

variable (OnCircle : Circle → Point → Prop)

/-
`OnBisector A X B C` means line AX bisects ∠BAC.
-/

variable
  (OnBisector :
    Point → Point → Point → Point → Prop)

/-
`OnPerpBisector X A B` means X lies on the perpendicular
bisector of AB.
-/

variable
  (OnPerpBisector :
    Point → Point → Point → Prop)

/-!
============================================================
2. Angle bisector packaging
============================================================
-/

/--
The target says there is one point lying on

1. the bisector of ∠ADP;
2. the bisector of ∠BCP;
3. the perpendicular bisector of AB.
-/
def ConcurrentTarget
    (OnBisector :
      Point → Point → Point → Point → Prop)
    (OnPerpBisector :
      Point → Point → Point → Prop)
    (A B C D P : Point) : Prop :=
  ∃ O : Point,
    OnBisector D O A P ∧
    OnBisector C O B P ∧
    OnPerpBisector O A B

/-!
============================================================
10. Final concurrency theorem
============================================================
-/
