namespace IMO1976P1

open Real

/-- The Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- The two–dimensional cross product of the vectors `Q - P` and `S - R`. -/
noncomputable def cross (P Q R S : Pt) : ℝ :=
  (Q 0 - P 0) * (S 1 - R 1) - (Q 1 - P 1) * (S 0 - R 0)

/-- Strict convexity of the quadrilateral `A B C D`, whose vertices are listed in
counterclockwise order: each consecutive turn is a strict left turn. -/
def ConvexCCW (A B C D : Pt) : Prop :=
  0 < cross A B B C ∧ 0 < cross B C C D ∧ 0 < cross C D D A ∧ 0 < cross D A A B

/-- The area of the quadrilateral `A B C D` (shoelace formula, valid for a
counterclockwise-oriented convex quadrilateral `A B C D`). -/
noncomputable def area (A B C D : Pt) : ℝ :=
  ((A 0 * B 1 - B 0 * A 1) + (B 0 * C 1 - C 0 * B 1) + (C 0 * D 1 - D 0 * C 1) +
    (D 0 * A 1 - A 0 * D 1)) / 2
