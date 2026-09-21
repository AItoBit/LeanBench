namespace IMO1984P4

/-- The algebraic core of Solution 2. -/

theorem candidate
  (AM DN d_M d_N : ℝ)
  (hAM_pos : 0 < AM)
  (tangent_CD : d_M = AM) :
  d_N = DN ↔ (1 / 2 : ℝ) * AM * d_N = (1 / 2 : ℝ) * DN * d_M :=
