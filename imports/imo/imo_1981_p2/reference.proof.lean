by
  have hcard : ((Finset.Icc 1 n).powersetCard r).card = n.choose r := by
    rw [Finset.card_powersetCard, Nat.card_Icc, Nat.add_sub_cancel]
  have hsum : (∑ S ∈ (Finset.Icc 1 n).powersetCard r, (smallest S : ℚ))
      = ((n + 1).choose (r + 1) : ℚ) := by
    rw [← Nat.cast_sum, sum_smallest n r hr]
  have hkey : (n + 1) * n.choose r = (n + 1).choose (r + 1) * (r + 1) :=
    Nat.add_one_mul_choose_eq n r
  have hne : (n.choose r : ℚ) ≠ 0 := by
    have : 0 < n.choose r := Nat.choose_pos hrn
    positivity
  have hr1 : ((r : ℚ) + 1) ≠ 0 := by positivity
  rw [hsum, hcard]
  rw [div_eq_div_iff hne hr1]
  have := congrArg (fun m : ℕ => (m : ℚ)) hkey
  push_cast at this ⊢
  linarith [this]
