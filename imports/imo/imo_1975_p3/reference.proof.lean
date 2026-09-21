by
  have hkey : Q - R = Complex.I * (P - R) := quarter_turn horient hPB hPC hQC hQA hRA hRB
  have hRP : R ≠ P := R_ne_P horient hPB hPC hRA hRB
  refine ⟨hRP, ?_, ?_, ?_⟩
  · intro h
    apply hRP
    have h0 : Complex.I * (P - R) = 0 := by rw [← hkey, ← h]; ring
    rcases mul_eq_zero.mp h0 with h' | h'
    · exact absurd h' Complex.I_ne_zero
    · exact (sub_eq_zero.mp h').symm
  · rw [EuclideanGeometry.angle, vsub_eq_sub, vsub_eq_sub,
      ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two, hkey]
    simp
    ring
  · rw [Complex.dist_eq, Complex.dist_eq, hkey, norm_mul, Complex.norm_I, one_mul, norm_sub_rev]
