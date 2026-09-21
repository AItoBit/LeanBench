by
  ext ⟨p₁, p₂, p₃, p₄, p₅⟩
  simp only [Set.mem_ofPred_eq, Set.mem_union, Prod.mk.injEq]
  constructor
  · rintro ⟨x₁, x₂, x₃, x₄, x₅, y, h₀, h₁, h₂, h₃, h₄, e₁, e₂, e₃, e₄, e₅⟩
    subst e₁; subst e₂; subst e₃; subst e₄; subst e₅
    -- `x₃, x₄, x₅` are determined by `x₁, x₂` and `y` via the recurrence
    have hx₃ : x₃ = y * x₂ - x₁ := by linarith
    subst hx₃
    have hx₄ : x₄ = y * (y * x₂ - x₁) - x₂ := by linear_combination h₂
    subst hx₄
    have hx₅ : x₅ = y * (y * (y * x₂ - x₁) - x₂) - (y * x₂ - x₁) := by
      linear_combination h₃
    subst hx₅
    by_cases hq : y ^ 2 + y - 1 = 0
    · -- golden ratio case: the tuple has exactly the stated shape
      right
      exact ⟨x₁, x₂, y, (imo_1963_p4_quadratic_iff y).mp hq, rfl, rfl, by ring,
        by linear_combination (-x₂) * hq,
        by linear_combination (x₁ - x₂ * (y - 1)) * hq⟩
    · -- otherwise the tuple is constant: either all zero, or `y = 2`
      left
      -- the two remaining (wrap-around) equations, factored
      have E2 : (y ^ 2 + y - 1) * (x₂ * (y - 1) - x₁) = 0 := by linear_combination h₀
      have E1 : (y ^ 2 + y - 1) * (x₂ * (y ^ 2 - y - 1) - x₁ * (y - 1)) = 0 := by
        linear_combination -h₄
      have hb2 : x₂ * (y - 1) - x₁ = 0 := by
        rcases mul_eq_zero.mp E2 with h | h
        · exact absurd h hq
        · exact h
      have hb1 : x₂ * (y ^ 2 - y - 1) - x₁ * (y - 1) = 0 := by
        rcases mul_eq_zero.mp E1 with h | h
        · exact absurd h hq
        · exact h
      have hx₁ : x₁ = x₂ * (y - 1) := by linarith
      have hy2 : x₂ * (y - 2) = 0 := by linear_combination hb1 + (y - 1) * hx₁
      rcases mul_eq_zero.mp hy2 with hb | hy
      · -- `x₂ = 0`, hence every coordinate vanishes
        have h1 : x₁ = 0 := by rw [hx₁, hb]; ring
        subst h1; subst hb
        exact ⟨0, rfl, rfl, by ring, by ring, by ring⟩
      · -- `y = 2`, hence the tuple is constant
        have hy' : y = 2 := by linarith
        subst hy'
        have h1 : x₁ = x₂ := by rw [hx₁]; ring
        refine ⟨x₁, rfl, ?_, ?_, ?_, ?_⟩ <;> linarith
  · rintro (⟨a, e₁, e₂, e₃, e₄, e₅⟩ | ⟨a, b, y, hy, e₁, e₂, e₃, e₄, e₅⟩)
    · subst e₁; subst e₂; subst e₃; subst e₄; subst e₅
      exact ⟨a, a, a, a, a, 2, by ring, by ring, by ring, by ring, by ring,
        rfl, rfl, rfl, rfl, rfl⟩
    · subst e₁; subst e₂; subst e₃; subst e₄; subst e₅
      have hq : y ^ 2 + y - 1 = 0 := (imo_1963_p4_quadratic_iff y).mpr hy
      exact ⟨a, b, -a + y * b, -y * a - y * b, y * a - b, y,
        by ring, by ring, by linear_combination (-b) * hq,
        by linear_combination (a + b) * hq, by linear_combination (-a) * hq,
        rfl, rfl, rfl, rfl, rfl⟩
