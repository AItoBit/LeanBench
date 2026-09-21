by
  by_contra hcon
  push_neg at hcon
  have hc : SumFreeColoring c := by
    intro x y hx hy hxy h1 h2
    have hx' : x ∈ Finset.Icc 1 1978 := Finset.mem_Icc.mpr ⟨hx, by omega⟩
    have hy' : y ∈ Finset.Icc 1 1978 := Finset.mem_Icc.mpr ⟨hy, by omega⟩
    have hz' : x + y ∈ Finset.Icc 1 1978 := Finset.mem_Icc.mpr ⟨by omega, hxy⟩
    exact absurd h2 (hcon x y (x + y) hx' hy' hz' rfl h1)
  have h0 : Inv c (Finset.Icc 1 1978) ∅ := by
    refine ⟨?_, ?_, ?_⟩
    · intro t ht
      rw [Finset.mem_Icc] at ht
      omega
    · intro t _; simp
    · intro t _ t' _ _; simp
  have hcard0 : (Finset.Icc 1 1978).card = 1978 := by simp
  obtain ⟨T1, F1, i1, f1, s1⟩ := step c hc _ ∅ 329 h0 (by simp [hcard0])
  obtain ⟨T2, F2, i2, f2, s2⟩ := step c hc T1 F1 65 i1 (by omega)
  obtain ⟨T3, F3, i3, f3, s3⟩ := step c hc T2 F2 16 i2 (by omega)
  obtain ⟨T4, F4, i4, f4, s4⟩ := step c hc T3 F3 5 i3 (by omega)
  obtain ⟨T5, F5, i5, f5, s5⟩ := step c hc T4 F4 2 i4 (by omega)
  obtain ⟨T6, F6, i6, f6, s6⟩ := step c hc T5 F5 1 i5 (by omega)
  -- now `F6` contains all six colours, yet `T6` is nonempty
  have hF6 : F6 = Finset.univ := by
    apply Finset.eq_univ_of_card
    simp [f6, f5, f4, f3, f2, f1]
  obtain ⟨t, ht⟩ : T6.Nonempty := Finset.card_pos.mp (by omega)
  exact i6.2.1 t ht (by simp [hF6])
