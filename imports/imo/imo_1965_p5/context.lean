namespace IMO1965P5

noncomputable section

/-- The Euclidean dot product on the coordinate plane `ℝ × ℝ`. -/
def dot (u v : ℝ × ℝ) : ℝ := u.1 * v.1 + u.2 * v.2

/-- The foot of the perpendicular dropped from `M` to the `x`-axis, i.e. to the
line `OA` with `O = (0,0)` and `A = (a, 0)`, `a ≠ 0`. -/
def footX (M : ℝ × ℝ) : ℝ × ℝ := (M.1, 0)

/-- The foot of the perpendicular dropped from `M` to the line `OB`
(with `O = (0,0)` and `B ≠ 0`). -/
def footLine (B M : ℝ × ℝ) : ℝ × ℝ := (dot M B / dot B B) • B

/-- `H` is the point of intersection of the altitudes (the orthocenter) of the
triangle `O P Q`: each of the three lines `OH`, `PH`, `QH` is perpendicular to
the opposite side. -/
def IsOrthocenter (O P Q H : ℝ × ℝ) : Prop :=
  dot (H - O) (P - Q) = 0 ∧ dot (H - P) (Q - O) = 0 ∧ dot (H - Q) (O - P) = 0

/-- The explicit formula for the orthocenter `H` of the triangle `OPQ`, as a
function of the point `M`, where `B = (b, c)`. -/
def Hpt (b c : ℝ) (M : ℝ × ℝ) : ℝ × ℝ :=
  (b * (M.1 * b + M.2 * c) / (b ^ 2 + c ^ 2), b * (M.1 * c - M.2 * b) / (b ^ 2 + c ^ 2))

/-- The "open triangle" with vertices `0`, `X`, `Y`: the set of strictly
positive convex combinations, i.e. the interior of the triangle `0 X Y` when
`X` and `Y` are linearly independent. -/
def openTriangle (X Y : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ α + β < 1 ∧ p = α • X + β • Y}

/-! ### The feet of the perpendiculars are what they should be -/
