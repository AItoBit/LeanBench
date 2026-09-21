by
  constructor
  · -- an explicit sequence of 16 terms
    refine ⟨fun k => if k = 2 ∨ k = 6 ∨ k = 9 ∨ k = 13 then (-13 : ℝ) else 5, ?_, ?_⟩
    · intro i hi
      have hi9 : i ≤ 9 := by omega
      interval_cases i <;> norm_num [Finset.sum_range_succ]
    · intro i hi
      have hi5 : i ≤ 5 := by omega
      interval_cases i <;> norm_num [Finset.sum_range_succ]
  · -- no sequence with 17 or more terms
    rintro n ⟨x, h7, h11⟩
    by_contra hcon
    have h17 : 17 ≤ n := by omega
    have A0 := h7 0 (by omega)
    have A1 := h7 1 (by omega)
    have A2 := h7 2 (by omega)
    have A3 := h7 3 (by omega)
    have A4 := h7 4 (by omega)
    have A5 := h7 5 (by omega)
    have A6 := h7 6 (by omega)
    have A7 := h7 7 (by omega)
    have A8 := h7 8 (by omega)
    have A9 := h7 9 (by omega)
    have A10 := h7 10 (by omega)
    have B0 := h11 0 (by omega)
    have B1 := h11 1 (by omega)
    have B2 := h11 2 (by omega)
    have B3 := h11 3 (by omega)
    have B4 := h11 4 (by omega)
    have B5 := h11 5 (by omega)
    have B6 := h11 6 (by omega)
    norm_num [Finset.sum_range_succ] at A0 A1 A2 A3 A4 A5 A6 A7 A8 A9 A10
    norm_num [Finset.sum_range_succ] at B0 B1 B2 B3 B4 B5 B6
    linarith
