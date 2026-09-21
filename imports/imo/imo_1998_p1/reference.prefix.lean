noncomputable section

namespace IMO1998P1

abbrev Point := ℝ × ℝ

def sqDist (U V : Point) : ℝ :=
  (U.1 - V.1)^2 + (U.2 - V.2)^2

def area (U V W : Point) : ℝ :=
  |(V.1 - U.1) * (W.2 - U.2) -
    (V.2 - U.2) * (W.1 - U.1)| / 2

def Cyclic (A B C D : Point) : Prop :=
  ∃ O : Point, ∃ r2 : ℝ, 0 < r2 ∧
    sqDist A O = r2 ∧ sqDist B O = r2 ∧
    sqDist C O = r2 ∧ sqDist D O = r2

/-
The supplied PDF is IMO 1998 Problem 1 (not 1988).

Coordinate formulation: put the diagonal intersection at the origin and
choose the perpendicular diagonals as coordinate axes. Then
  A = (a,0), B = (0,b), C = (-c,0), D = (0,-d), P = (x,y),
with a,b,c,d positive. This file proves the theorem in those coordinates;
it does not formalize the change of coordinates from an abstract Euclidean plane.

Inside gives the four strict half-plane conditions for interior membership.
a*d-b*c is the determinant of the direction vectors of AB and CD.
The two sqDist equalities express membership in their perpendicular bisectors.
Cyclic means membership of all four points in a circle of positive radius
squared; area is the ordinary unsigned triangle area.
-/

/-- With the diagonal intersection as origin and the diagonals as axes,
    the vertices are (a,0), (0,b), (-c,0), (0,-d). -/
theorem cyclic_iff (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Cyclic (a,0) (0,b) (-c,0) (0,-d) ↔ a*c = b*d := by
  constructor
  · rintro ⟨⟨u,v⟩, r, _, hA, hB, hC, hD⟩
    dsimp [sqDist] at hA hB hC hD
    have hu : 2*u = a-c := by
      have h : (a+c) * (2*u-a+c) = 0 := by nlinarith [hA, hC]
      have hn : a+c ≠ 0 := ne_of_gt (add_pos ha hc)
      have := (mul_eq_zero.mp h).resolve_left hn
      linarith
    have hBD : (b+d) * (2*v-b+d) = 0 := by nlinarith [hB, hD]
    have hv : 2*v = b-d := by
      have hn : b+d ≠ 0 := ne_of_gt (add_pos hb hd)
      have := (mul_eq_zero.mp hBD).resolve_left hn
      linarith
    nlinarith [hA, hB]
  · intro h
    refine ⟨((a-c)/2, (b-d)/2),
      sqDist (a,0) ((a-c)/2, (b-d)/2), ?_, rfl, ?_, ?_, ?_⟩
    · dsimp [sqDist]
      have : 0 < a - (a-c)/2 := by linarith
      nlinarith [sq_pos_of_pos this, sq_nonneg ((0:ℝ)-(b-d)/2)]
    all_goals dsimp [sqDist]; nlinarith

/-- P is strictly inside the quadrilateral, expressed by its four side inequalities. -/
def Inside (a b c d x y : ℝ) : Prop :=
  0 < a*b - b*x - a*y ∧
  0 < b*c + b*x - c*y ∧
  0 < c*d + d*x + c*y ∧
  0 < a*d - d*x + a*y
