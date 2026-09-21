open scoped Classical

namespace IMO1969P5

/-- Points of the plane. -/
abbrev Pt := ℝ × ℝ

/-- Twice the signed area of the triangle `a b c`; it vanishes exactly when `a`, `b`, `c` are
collinear. -/
def det3 (a b c : Pt) : ℝ := (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- No three distinct points of `S` are collinear. -/
def NoThreeCollinear (S : Finset Pt) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c → det3 a b c ≠ 0

/-- A finite set of points is in *convex position* if none of its points lies in the convex hull
of the remaining ones. -/
def InConvexPosition (T : Finset Pt) : Prop :=
  ∀ p ∈ T, p ∉ convexHull ℝ ((T.erase p : Finset Pt) : Set Pt)

/-! ### Convex hulls of triples -/
