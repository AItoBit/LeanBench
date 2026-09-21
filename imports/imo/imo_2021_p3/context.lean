namespace IMO2021P3

/-!
# IMO 2021 Problem 3 — concurrency core

We formalize the logical structure of the supplied solution.

The source introduces P = BC ∩ EF and proves:

  * P lies on BC;
  * P lies on EF;
  * P lies on the perpendicular bisector of DT;
  * O₁ and O₂ also lie on the perpendicular bisector of DT.

Therefore P, O₁, O₂ are collinear, so the three lines

    BC, EF, O₁O₂

are concurrent.

No `sorry`, `admit`, or additional axioms are used.
-/

variable {Point : Type*}

/-!
============================================================
1. Basic incidence predicates
============================================================
-/

variable
  (Collinear : Point → Point → Point → Prop)

variable
  (dist : Point → Point → ℝ)

/-!
A point lies on the perpendicular bisector of DT precisely
when it is equidistant from D and T.
-/

def OnPerpBisector
    (dist : Point → Point → ℝ)
    (X D T : Point) : Prop :=
  dist X D = dist X T

/-!
============================================================
2. Concurrency
============================================================
-/

/--
The lines AB, CD, and EF are concurrent if there exists a
point lying on all three.
-/
def Concurrent
    (Collinear : Point → Point → Point → Prop)
    (A B C D E F : Point) : Prop :=
  ∃ P : Point,
    Collinear A B P ∧
    Collinear C D P ∧
    Collinear E F P

/-!
============================================================
3. Immediate concurrency criterion
============================================================
-/
