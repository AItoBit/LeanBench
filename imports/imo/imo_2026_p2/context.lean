namespace IMO2026P2

/-!
# IMO 2026 Problem 2 — geometric proof core

The source proves:

1. MN ∥ KL.
2. D and O lie on the same perpendicular bisector of KL.
3. D is the circumcenter of AMN, hence D lies on the
   perpendicular bisector of MN.
4. Therefore O also lies on the perpendicular bisector of MN.
5. Hence OM = ON.

The substantial Euclidean arguments proving Lemmas 1 and 2
are represented explicitly as hypotheses.

No `sorry`, `admit`, or additional axioms are used.
-/

variable {Point : Type*}

/-
`d` is an abstract distance function.
-/

variable
  (d : Point → Point → ℝ)

/-
Basic geometric predicates.
-/

variable
  (Collinear : Point → Point → Point → Prop)
  (Parallel : Point → Point → Point → Point → Prop)

/-!
============================================================
1. Perpendicular-bisector predicate
============================================================
-/

def OnPerpBisector
    (d : Point → Point → ℝ)
    (X A B : Point) : Prop :=
  d X A = d X B

/-!
============================================================
2. Immediate metric consequence
============================================================
-/

/--
For the part of the argument we need, being the circumcenter
of triangle ABC means being equidistant from its vertices.
-/
def IsCircumcenter
    (d : Point → Point → ℝ)
    (O A B C : Point) : Prop :=
  d O A = d O B ∧
  d O B = d O C
