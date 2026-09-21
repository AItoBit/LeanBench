by
  have hme : (m : ℤ) = expo n := by
    have := expo_closed n
    omega
  have hpos : 1 ≤ expo n := expo_pos n hn
  have hval : u n = (2 : ℝ) ^ (expo n) + (2 : ℝ) ^ (-(expo n)) := u_eq n
  have hint : (2 : ℝ) ^ (expo n) = ((2 ^ m : ℤ) : ℝ) := by
    rw [← hme]
    push_cast
    rw [← zpow_natCast (2 : ℝ) m]
  have hsmall1 : (0 : ℝ) < (2 : ℝ) ^ (-(expo n)) := zpow_pos (by norm_num) _
  have hsmall2 : (2 : ℝ) ^ (-(expo n)) < 1 := by
    apply zpow_lt_one_of_neg₀ (by norm_num) (by omega)
  rw [hval, hint, Int.floor_eq_iff]
  refine ⟨by push_cast; linarith, by push_cast; linarith⟩
