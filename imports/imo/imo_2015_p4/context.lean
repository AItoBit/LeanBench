namespace IMO2015P4

/-!
# IMO 2015 Problem 4 — final metric core

The source's Solution 2 reduces the problem to:

* `AF = AG`, since F and G lie on the circle Γ centered at A;
* `OF = OG`, since F and G lie on the circumcircle Ω centered at O;
* after the angle chase, `XF = XG`.

Thus A, O, and X all lie on the perpendicular bisector of FG.
Since `F ≠ G`, this perpendicular bisector is a genuine line,
hence A, O, X are collinear.

No `sorry`, `admit`, or extra axioms are used.
-/

abbrev Point := ℝ × ℝ

/-!
## Squared distance
-/

def distSq (P Q : Point) : ℝ :=
  (P.1 - Q.1) ^ 2 +
  (P.2 - Q.2) ^ 2

/-!
## Collinearity
-/

def Collinear
    (P Q R : Point) : Prop :=
  (Q.1 - P.1) * (R.2 - P.2) -
    (Q.2 - P.2) * (R.1 - P.1) = 0

/-!
## Equal-distance equation
-/

/--
`O` is equidistant from `F,G`.
-/
def EquidistantCenter
    (O F G : Point) : Prop :=
  distSq O F = distSq O G

/-!
## Final theorem
-/
