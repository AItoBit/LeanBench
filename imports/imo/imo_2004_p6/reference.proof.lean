by
  rintro ⟨m, hmpos, hnm, halt⟩
  exact not_alternating_of_twenty_dvd hmpos (dvd_trans h hnm) halt

/-! ### Arithmetic of writing one block in front of another -/
