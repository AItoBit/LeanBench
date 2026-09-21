by
  have hM : ((Mset n k).card : ℚ) ≠ 0 := by
    exact_mod_cast (card_Mset_pos hn hk he).ne'
  rw [card_Nset_eq_mul_card_Mset]
  push_cast
  field_simp
