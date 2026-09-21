by
  have hnonempty : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  constructor
  · -- if the points can be pushed arbitrarily far, then `k ≥ 1/(N-1)`
    intro h
    by_contra hcon
    push Not at hcon
    have hprod : k * ((N : ℝ) - 1) < 1 := by
      have h1 : k * ((N : ℝ) - 1) < (1 / ((N : ℝ) - 1)) * ((N : ℝ) - 1) :=
        mul_lt_mul_of_pos_right hcon hN1
      rwa [one_div, inv_mul_cancel₀ (ne_of_gt hN1)] at h1
    have hk0 : 0 < 1 / k - ((N : ℝ) - 1) := by
      have heq : 1 / k - ((N : ℝ) - 1) = (1 - k * ((N : ℝ) - 1)) / k := by field_simp
      rw [heq]
      exact div_pos (by linarith) hk
    obtain ⟨y, hy, hy2⟩ :=
      h (fun l => if l = (⟨0, by omega⟩ : Fin N) then 0 else 1)
        ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by
          have h10 : (⟨1, by omega⟩ : Fin N) ≠ (⟨0, by omega⟩ : Fin N) := by
            rw [Ne, Fin.ext_iff]; norm_num
          simp [h10]⟩
        (Rmax (fun l => if l = (⟨0, by omega⟩ : Fin N) then 0 else 1) +
          Xpot (fun l => if l = (⟨0, by omega⟩ : Fin N) then 0 else 1) /
            (1 / k - ((N : ℝ) - 1)))
    have hbound := phi_reach hk hk0 rfl hy
    have hXy : 0 ≤ Xpot y / (1 / k - ((N : ℝ) - 1)) := div_nonneg (Xpot_nonneg y) hk0.le
    have h1 := hy2 (⟨0, by omega⟩ : Fin N)
    have h2 := le_Rmax y (⟨0, by omega⟩ : Fin N)
    linarith
  · -- if `k ≥ 1/(N-1)`, the points can be pushed arbitrarily far
    intro hkN x hx M
    have hkN' : 1 ≤ ((N : ℝ) - 1) * k := by
      have h1 : ((N : ℝ) - 1) * (1 / ((N : ℝ) - 1)) ≤ ((N : ℝ) - 1) * k :=
        mul_le_mul_of_nonneg_left hkN hN1.le
      rwa [mul_one_div, div_self (ne_of_gt hN1)] at h1
    have hX : 0 < Xpot x := by
      rcases (Xpot_nonneg x).lt_or_eq with hpos | heq
      · exact hpos
      · exfalso
        obtain ⟨i, j, hij⟩ := hx
        have hsum : ∑ l, (Rmax x - x l) = 0 := by rw [← Xpot_eq_sum]; linarith
        have hall := (Finset.sum_eq_zero_iff_of_nonneg
          (fun l _ => sub_nonneg.2 (le_Rmax x l))).1 hsum
        have h1 := hall i (Finset.mem_univ i)
        have h2 := hall j (Finset.mem_univ j)
        exact hij (by linarith)
    have hcpos : 0 < k * Xpot x / (N : ℝ) := by positivity
    have hcne : k * Xpot x / (N : ℝ) ≠ 0 := ne_of_gt hcpos
    obtain ⟨n, hn⟩ := exists_nat_gt ((M - Rmax x) / (k * Xpot x / (N : ℝ)))
    obtain ⟨y, hy, -, hRy⟩ := iterate hk hNr hkN' x hX n
    have hMy : M < Rmax y := by
      have h1 : ((M - Rmax x) / (k * Xpot x / (N : ℝ))) * (k * Xpot x / (N : ℝ))
          < (n : ℝ) * (k * Xpot x / (N : ℝ)) := mul_lt_mul_of_pos_right hn hcpos
      have h2 : ((M - Rmax x) / (k * Xpot x / (N : ℝ))) * (k * Xpot x / (N : ℝ))
          = M - Rmax x := by field_simp
      rw [h2] at h1
      linarith
    obtain ⟨z, hz1, hz2⟩ :=
      cleanup hk M ({i | y i ≤ M} : Finset (Fin N)).card y (le_refl _) hMy
    exact ⟨z, hy.trans hz1, hz2⟩
