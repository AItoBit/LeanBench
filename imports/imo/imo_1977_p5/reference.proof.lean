by
  constructor
  · rintro ⟨q, r, heq, hr, hqr⟩
    -- everything moves to `ℤ`
    have hq0 : (0 : ℤ) ≤ (q : ℤ) := by exact_mod_cast Nat.zero_le q
    have hr0 : (0 : ℤ) ≤ (r : ℤ) := by exact_mod_cast Nat.zero_le r
    have haZ : (1 : ℤ) ≤ (a : ℤ) := by exact_mod_cast ha
    have hbZ : (1 : ℤ) ≤ (b : ℤ) := by exact_mod_cast hb
    have heqZ : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = (q : ℤ) * ((a : ℤ) + (b : ℤ)) + (r : ℤ) := by
      exact_mod_cast heq
    have hrZ : (r : ℤ) < (a : ℤ) + (b : ℤ) := by exact_mod_cast hr
    have hqrZ : (q : ℤ) ^ 2 + (r : ℤ) = 1977 := by exact_mod_cast hqr
    -- `q = 44`, `r = 41`
    have hab := abbound haZ hbZ hrZ heqZ
    have h44 : (q : ℤ) = 44 := le_antisymm (qle hq0 hr0 hqrZ) (qge hq0 hqrZ hrZ hab)
    have hr41 : (r : ℤ) = 41 := by
      rw [h44] at hqrZ
      linarith
    have heq44 : a ^ 2 + b ^ 2 = 44 * (a + b) + 41 := by
      have hZ : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = 44 * ((a : ℤ) + (b : ℤ)) + 41 := by
        rw [h44, hr41] at heqZ
        exact heqZ
      exact_mod_cast hZ
    -- `(a-22)² + (b-22)² = 1009`
    have hsum : ((a : ℤ) - 22) ^ 2 + ((b : ℤ) - 22) ^ 2 = 1009 := by
      have hZ : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = 44 * ((a : ℤ) + (b : ℤ)) + 41 := by
        exact_mod_cast heq44
      linear_combination hZ
    have hsum' : ((b : ℤ) - 22) ^ 2 + ((a : ℤ) - 22) ^ 2 = 1009 := by linarith
    have ha54 : a < 54 := by
      have h := sq_bound hsum
      omega
    have hb54 : b < 54 := by
      have h := sq_bound hsum'
      omega
    exact enum a (Finset.mem_range.mpr ha54) b (Finset.mem_range.mpr hb54) heq44
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      exact ⟨44, 41, by norm_num, by norm_num, by norm_num⟩
