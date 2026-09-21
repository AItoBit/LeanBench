by
  obtain ⟨k, hk⟩ := imo1988_q6 a b ha hb hdvd
  refine ⟨k, ?_⟩
  rw [hk, Nat.mul_div_cancel _ (Nat.succ_pos _)]
  ring
