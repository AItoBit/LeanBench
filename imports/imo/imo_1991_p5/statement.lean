namespace IMO1991P5

abbrev Point := ℝ × ℝ

def orient (A B P : Point) : ℝ :=
  (B.1 - A.1) * (P.2 - A.2) - (B.2 - A.2) * (P.1 - A.1)

def dotAt (A B P : Point) : ℝ :=
  (B.1 - A.1) * (P.1 - A.1) + (B.2 - A.2) * (P.2 - A.2)

/-- Algebraic form of `∠PAB ≤ 30°`. -/

def angleLE30 (P A B : Point) : Prop :=
  Real.sqrt 3 * |orient A B P| ≤ dotAt A B P

/-- Strict barycentric interior, allowing either orientation of the vertices. -/

def StrictlyInside (P A B C : Point) : Prop :=
  (0 < orient A B P ∧ 0 < orient B C P ∧ 0 < orient C A P) ∨
  (orient A B P < 0 ∧ orient B C P < 0 ∧ orient C A P < 0)

theorem candidate (A B C P : Point) (hP : StrictlyInside P A B C) :
    angleLE30 P A B ∨ angleLE30 P B C ∨ angleLE30 P C A :=
