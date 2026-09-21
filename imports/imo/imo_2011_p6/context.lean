namespace IMO2011P6

abbrev Point := ℝ × ℝ

/-! ## Elementary coordinate operations -/

/-- Squared Euclidean norm. -/
def sqNorm (P : Point) : ℝ :=
  P.1 ^ 2 + P.2 ^ 2

/-- Dot product. -/
def dot (P Q : Point) : ℝ :=
  P.1 * Q.1 + P.2 * Q.2

/-- Scalar multiplication of a point/vector. -/
def scale (t : ℝ) (P : Point) : Point :=
  (t * P.1, t * P.2)

/-- Squared Euclidean distance. -/
def sqDist (P Q : Point) : ℝ :=
  (P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2

/-- Membership in the unit circle centered at `(0,0)`. -/
def OnUnitCircle (P : Point) : Prop :=
  sqNorm P = 1

/--
Membership in a circle specified by its center and squared radius.
-/
def OnCircleSq
    (C : Point)
    (r2 : ℝ)
    (P : Point) : Prop :=
  sqDist P C = r2

/-!
## The normalized tangent `y = 1`
-/

/--
Two circles are tangent at `P` in the set-theoretic sense used here
if `P` lies on both circles and is their unique common point.
-/
def TangentToUnitAt
    (C : Point)
    (r2 : ℝ)
    (P : Point) : Prop :=
  OnUnitCircle P ∧
  OnCircleSq C r2 P ∧
  ∀ Q : Point,
    OnUnitCircle Q →
    OnCircleSq C r2 Q →
    Q = P
