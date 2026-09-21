/-- The configuration described in the problem does occur: there are circles, tangency points
and midpoints satisfying all the hypotheses of `angle_O1AO2_eq_angle_M1AM2`. -/
theorem candidate :
    ∃ (O1 O2 A P1 P2 Q1 Q2 M1 M2 : Plane) (r1 r2 : ℝ),
      0 < r1 ∧ 0 < r2 ∧ r1 ≠ r2 ∧
      dist A O1 = r1 ∧ dist A O2 = r2 ∧
      dist P1 O1 = r1 ∧ dist P2 O2 = r2 ∧ dist Q1 O1 = r1 ∧ dist Q2 O2 = r2 ∧
      P1 ≠ P2 ∧ ⟪P1 - O1, P2 - P1⟫ = 0 ∧ ⟪P2 - O2, P2 - P1⟫ = 0 ∧
      Q1 ≠ Q2 ∧ ⟪Q1 - O1, Q2 - Q1⟫ = 0 ∧ ⟪Q2 - O2, Q2 - Q1⟫ = 0 ∧
      P1 ≠ Q1 ∧ M1 = midpoint ℝ P1 Q1 ∧ M2 = midpoint ℝ P2 Q2 :=
