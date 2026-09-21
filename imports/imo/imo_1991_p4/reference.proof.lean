by
  -- Let d be any common divisor of all incident labels
  intro d hd
  
  -- Since d divides all incident labels, it must divide n and n + 1
  have h_n : d ∣ n := hd n hn
  have h_succ : d ∣ n + 1 := hd (n + 1) hsucc
  
  -- In Lean 4, Nat.dvd_sub takes exactly two divisibility proofs.
  -- It divides the difference unconditionally.
  have h_diff : d ∣ (n + 1) - n := Nat.dvd_sub h_succ h_n
  
  -- The difference is 1
  have h_one : (n + 1) - n = 1 := by omega
  
  -- Therefore, d divides 1, which means d = 1
  rw [h_one] at h_diff
  exact Nat.eq_one_of_dvd_one h_diff
