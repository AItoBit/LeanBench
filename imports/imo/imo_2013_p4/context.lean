namespace IMO2013P4

/-!
## Coordinate geometry
-/

abbrev Point := ℝ × ℝ

/-- Difference of two points, viewed as a vector. -/
def vec (P Q : Point) : Point :=
  (Q.1 - P.1, Q.2 - P.2)

/-- Two-dimensional determinant / cross product. -/
def cross (u v : Point) : ℝ :=
  u.1 * v.2 - u.2 * v.1

/--
Three points are collinear when the determinant of the
two displacement vectors is zero.
-/
def Collinear (P Q R : Point) : Prop :=
  cross (vec P Q) (vec P R) = 0

/-!
## Elementary coordinate lemmas
-/
