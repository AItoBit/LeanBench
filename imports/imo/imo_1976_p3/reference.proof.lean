by
  set x := ⌊(a : ℝ) / cbrt2⌋₊ with hxdef
  set y := ⌊(b : ℝ) / cbrt2⌋₊ with hydef
  set z := ⌊(c : ℝ) / cbrt2⌋₊ with hzdef
  have hnat : (2 * ((x : ℝ) * (y : ℝ) * (z : ℝ)) = (2 / 5) * ((a : ℝ) * (b : ℝ) * (c : ℝ))) ↔
      5 * (x * y * z) = a * b * c := by
    constructor
    · intro h
      have : ((5 * (x * y * z) : ℕ) : ℝ) = ((a * b * c : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    · intro h
      have : ((5 * (x * y * z) : ℕ) : ℝ) = ((a * b * c : ℕ) : ℝ) := by exact_mod_cast h
      push_cast at this
      linarith
  rw [hnat]
  obtain ⟨hax1, hax2⟩ := (floor_cbrt2_spec a x).mp hxdef.symm
  obtain ⟨hby1, hby2⟩ := (floor_cbrt2_spec b y).mp hydef.symm
  obtain ⟨hcz1, hcz2⟩ := (floor_cbrt2_spec c z).mp hzdef.symm
  constructor
  · intro hvol
    exact arith_solution ha hb hc hax1 hax2 hby1 hby2 hcz1 hcz2 hvol
  · intro hmul
    have hcases :
        (a = 2 ∧ b = 3 ∧ c = 5) ∨ (a = 2 ∧ b = 5 ∧ c = 3) ∨ (a = 3 ∧ b = 2 ∧ c = 5) ∨
          (a = 3 ∧ b = 5 ∧ c = 2) ∨ (a = 5 ∧ b = 2 ∧ c = 3) ∨ (a = 5 ∧ b = 3 ∧ c = 2) ∨
          (a = 2 ∧ b = 5 ∧ c = 6) ∨ (a = 2 ∧ b = 6 ∧ c = 5) ∨ (a = 5 ∧ b = 2 ∧ c = 6) ∨
          (a = 5 ∧ b = 6 ∧ c = 2) ∨ (a = 6 ∧ b = 2 ∧ c = 5) ∨ (a = 6 ∧ b = 5 ∧ c = 2) := by
      rcases hmul with h | h
      · simp [Multiset.cons_eq_cons] at h
        rcases h with ⟨rfl, h⟩ | ⟨hne, cs, h1, h2⟩
        · omega
        · rcases h1 with ⟨rfl, rfl⟩ | ⟨h3, rfl, rfl⟩ <;> simp_all <;> omega
      · simp [Multiset.cons_eq_cons] at h
        rcases h with ⟨rfl, h⟩ | ⟨hne, cs, h1, h2⟩
        · omega
        · rcases h1 with ⟨rfl, rfl⟩ | ⟨h3, rfl, rfl⟩ <;> simp_all <;> omega
    have hx2 : x = ⌊((a : ℕ) : ℝ) / cbrt2⌋₊ := hxdef
    have hy2 : y = ⌊((b : ℕ) : ℝ) / cbrt2⌋₊ := hydef
    have hz2 : z = ⌊((c : ℕ) : ℝ) / cbrt2⌋₊ := hzdef
    rcases hcases with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      simp only [hx2, hy2, hz2, floor_two, floor_three, floor_five, floor_six] <;>
      norm_num
