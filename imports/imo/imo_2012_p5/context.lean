namespace IMO2012P5

abbrev Point := ℝ × ℝ

/-! ## Basic coordinate geometry -/

/-- Squared Euclidean distance. -/
def sqDist (P Q : Point) : ℝ :=
  (P.1 - Q.1) ^ 2 +
  (P.2 - Q.2) ^ 2

/--
Dot product of the vectors `RP` and `RQ`.
-/
def dotAt (R P Q : Point) : ℝ :=
  (P.1 - R.1) * (Q.1 - R.1) +
  (P.2 - R.2) * (Q.2 - R.2)

/--
Euclidean distance, defined from squared distance.
-/
noncomputable def distance (P Q : Point) : ℝ :=
  Real.sqrt (sqDist P Q)

/-!
## Elementary distance identities
-/
