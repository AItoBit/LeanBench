by
  classical
  -- the `j`-th plane is `x = j+1` for `j < n`, `y = j+1-n` for `n ≤ j < 2n`,
  -- and `z = j+1-2n` for `2n ≤ j`.
  refine ⟨fun j => if (j : ℕ) < n then 1 else 0,
          fun j => if n ≤ (j : ℕ) ∧ (j : ℕ) < 2 * n then 1 else 0,
          fun j => if 2 * n ≤ (j : ℕ) then 1 else 0,
          fun j => if (j : ℕ) < n then (((j : ℕ) + 1 : ℕ) : ℝ)
            else if (j : ℕ) < 2 * n then (((j : ℕ) + 1 - n : ℕ) : ℝ)
            else (((j : ℕ) + 1 - 2 * n : ℕ) : ℝ), ?_, ?_, ?_⟩
  · intro j
    rcases lt_or_ge (j : ℕ) n with h | h
    · simp [h]
    · rcases lt_or_ge (j : ℕ) (2 * n) with h' | h'
      · simp [Nat.not_lt.mpr h, h, h']
      · simp [Nat.not_lt.mpr h, h']
  · rintro p ⟨x, y, z, hx, hy, hz, hpos, rfl⟩
    simp only [Set.mem_iUnion, mem_planeSet]
    rcases Nat.eq_zero_or_pos x with hx0 | hx0
    · rcases Nat.eq_zero_or_pos y with hy0 | hy0
      · -- z > 0
        have hz0 : 0 < z := by omega
        have hjlt : 2 * n + z - 1 < 3 * n := by omega
        refine ⟨⟨2 * n + z - 1, hjlt⟩, ?_⟩
        have h1 : ¬ (2 * n + z - 1 < n) := by omega
        have h2 : ¬ (2 * n + z - 1 < 2 * n) := by omega
        have h3 : 2 * n ≤ 2 * n + z - 1 := by omega
        have h4 : 2 * n + z - 1 + 1 - 2 * n = z := by omega
        simp only [h1, h2, h3, h4, ite_true, ite_false, hx0, hy0]
        norm_num
      · have hjlt : n + y - 1 < 3 * n := by omega
        refine ⟨⟨n + y - 1, hjlt⟩, ?_⟩
        have h1 : ¬ (n + y - 1 < n) := by omega
        have h2 : n + y - 1 < 2 * n := by omega
        have h3 : n ≤ n + y - 1 := by omega
        have h4 : n + y - 1 + 1 - n = y := by omega
        have h5 : ¬ (2 * n ≤ n + y - 1) := by omega
        simp only [h1, h2, h3, h4, h5, ite_true, ite_false, hx0, and_self]
        norm_num
    · have hjlt : x - 1 < 3 * n := by omega
      refine ⟨⟨x - 1, hjlt⟩, ?_⟩
      have h1 : x - 1 < n := by omega
      have h4 : x - 1 + 1 = x := by omega
      have h5 : ¬ (n ≤ x - 1 ∧ x - 1 < 2 * n) := by omega
      have h6 : ¬ (2 * n ≤ x - 1) := by omega
      simp only [h1, h4, h5, h6, ite_true, ite_false]
      norm_num
  · simp only [Set.mem_iUnion, mem_planeSet, not_exists]
    intro j
    have hne : ∀ k : ℕ, 0 < k → (0 : ℝ) ≠ (k : ℝ) := fun k hk => (Nat.cast_pos.mpr hk).ne
    simp only [mul_zero, add_zero]
    rcases lt_or_ge (j : ℕ) n with h | h
    · simpa only [h, ite_true] using hne ((j : ℕ) + 1) (by omega)
    · rcases lt_or_ge (j : ℕ) (2 * n) with h' | h'
      · have h1 : ¬ ((j : ℕ) < n) := by omega
        simpa only [h1, h', ite_true, ite_false] using hne ((j : ℕ) + 1 - n) (by omega)
      · have h1 : ¬ ((j : ℕ) < n) := by omega
        have h2 : ¬ ((j : ℕ) < 2 * n) := by omega
        simpa only [h1, h2, ite_false] using hne ((j : ℕ) + 1 - 2 * n) (by omega)
