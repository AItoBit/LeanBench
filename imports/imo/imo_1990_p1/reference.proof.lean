by
  obtain ⟨-, -, hratio⟩ := ratio_of_sbtw hM ht
  have hMB : 0 < dist M B := dist_pos.2 hM.ne_right
  rw [ratio_of_similar hMB hEC hEG hEF h₁ h₂]
  exact hratio
