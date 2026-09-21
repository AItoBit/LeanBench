namespace Imo1969P5

open Finset

/-- Twice the signed area of the triangle `a b c` in the plane. -/
def det (a b c : ℝ × ℝ) : ℝ := (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- A finite set of points is in general position if no three distinct points are collinear. -/
def GenPos (S : Finset (ℝ × ℝ)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c → det a b c ≠ 0

/-- A four-element set of points in convex position: no point lies in the convex hull of
the other three.  These are exactly the vertex sets of convex quadrilaterals. -/
def ConvexQuad (s : Finset (ℝ × ℝ)) : Prop :=
  s.card = 4 ∧ ∀ x ∈ s, x ∉ convexHull ℝ (↑(s.erase x) : Set (ℝ × ℝ))

/-! ### Basic determinant identities -/
