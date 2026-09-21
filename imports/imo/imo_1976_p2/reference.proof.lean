by
  have hQ0 : P n - Polynomial.X ≠ 0 := P_sub_X_ne_zero n hn
  obtain ⟨-, hcard, hnodup⟩ := imo1976_p2 n hn
  have hset : {x : ℝ | (P n).eval x = x} = ((P n - Polynomial.X).roots.toFinset : Set ℝ) := by
    ext x
    simp [Multiset.mem_toFinset, Polynomial.mem_roots hQ0, sub_eq_zero]
  rw [hset, Set.ncard_coe_finset, Multiset.toFinset_card_eq_card_iff_nodup.mpr hnodup, hcard]
