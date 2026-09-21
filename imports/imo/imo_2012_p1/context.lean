namespace IMO2012P1

abbrev Point := ℝ × ℝ

/-!
## Basic coordinate geometry
-/

/-- Squared Euclidean distance. -/
def sqDist (P Q : Point) : ℝ :=
  (P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2

/--
Euclidean midpoint in coordinates.

This is `noncomputable` because division on real numbers is
noncomputable in Lean.
-/
noncomputable def midpoint (P Q : Point) : Point :=
  ((P.1 + Q.1) / 2, (P.2 + Q.2) / 2)

/-!
## One-dimensional midpoint lemma
-/

/--
The part of "J is the circumcenter of AST" needed for the
final step: J is equally distant from S and T.
-/
def EquidistantFromST
    (J S T : Point) : Prop :=
  sqDist J S = sqDist J T
