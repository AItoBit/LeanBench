namespace IMO2013P3

/-!
## Coordinate metric layer
-/

abbrev Point := ℝ × ℝ

/-- Squared Euclidean distance. -/
def sqDist (P Q : Point) : ℝ :=
  (P.1 - Q.1) ^ 2 +
  (P.2 - Q.2) ^ 2

/--
A minimal circumcenter predicate:
`O` is equidistant from the three vertices.
-/
def IsCircumcenter
    (O A B C : Point) : Prop :=
  sqDist O A = sqDist O B ∧
  sqDist O B = sqDist O C

/-- 45 degrees in radians. -/
noncomputable def angle45 : ℝ :=
  Real.pi / 4

/-- 90 degrees in radians. -/
noncomputable def angle90 : ℝ :=
  Real.pi / 2

/-- 180 degrees in radians. -/
noncomputable def angle180 : ℝ :=
  Real.pi

/--
The final information supplied by the Bevan-point/Reim part
of the source proof.

`angleIcIaIb` represents `∠I_c I_a I_b`.
`angleA` represents `∠CAB`.
-/
structure FinalAngleData where
  angleIcIaIb : ℝ
  angleA : ℝ

  bevan_angle :
    angleIcIaIb = Real.pi / 4

  angle_relation :
    angleA =
      Real.pi - 2 * angleIcIaIb
