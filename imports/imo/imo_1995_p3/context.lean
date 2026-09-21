namespace EqualAreaLabelling

/-- Twice the signed area of the triangle `P Q R`. -/
def sdet (P Q R : ℝ × ℝ) : ℝ :=
  (Q.1 - P.1) * (R.2 - P.2) - (Q.2 - P.2) * (R.1 - P.1)

/-- The (unsigned) area of the triangle `P Q R`. -/
noncomputable def area (P Q R : ℝ × ℝ) : ℝ := |sdet P Q R| / 2
