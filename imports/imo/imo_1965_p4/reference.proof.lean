by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    -- Multiply the `i`-th equation by `xᵢ`: with `P = x₁x₂x₃x₄`, each `xᵢ` satisfies
    -- `xᵢ² - 2xᵢ + P = 0`.
    have e1 : x₁ ^ 2 - 2 * x₁ + x₁ * x₂ * x₃ * x₄ = 0 := by linear_combination x₁ * h1
    have e2 : x₂ ^ 2 - 2 * x₂ + x₁ * x₂ * x₃ * x₄ = 0 := by linear_combination x₂ * h2
    have e3 : x₃ ^ 2 - 2 * x₃ + x₁ * x₂ * x₃ * x₄ = 0 := by linear_combination x₃ * h3
    have e4 : x₄ ^ 2 - 2 * x₄ + x₁ * x₂ * x₃ * x₄ = 0 := by linear_combination x₄ * h4
    -- Two roots of the same monic quadratic: `xⱼ = x₁` or `xⱼ = 2 - x₁`.
    have c2 : x₂ = x₁ ∨ x₂ = 2 - x₁ := by
      have h : (x₁ - x₂) * (x₁ + x₂ - 2) = 0 := by linear_combination e1 - e2
      rcases mul_eq_zero.mp h with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    have c3 : x₃ = x₁ ∨ x₃ = 2 - x₁ := by
      have h : (x₁ - x₃) * (x₁ + x₃ - 2) = 0 := by linear_combination e1 - e3
      rcases mul_eq_zero.mp h with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    have c4 : x₄ = x₁ ∨ x₄ = 2 - x₁ := by
      have h : (x₁ - x₄) * (x₁ + x₄ - 2) = 0 := by linear_combination e1 - e4
      rcases mul_eq_zero.mp h with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    clear e1 e2 e3 e4
    rcases c2 with d2 | d2 <;> rcases c3 with d3 | d3 <;> rcases c4 with d4 | d4 <;>
      rw [d2, d3, d4] at h1 h2 h3 h4 ⊢
    -- Case 1: `(x₁, x₁, x₁, x₁)`.
    · have hx : (x₁ - 1) * (x₁ ^ 2 + x₁ + 2) = 0 := by linear_combination h1
      have hp : (0:ℝ) < x₁ ^ 2 + x₁ + 2 := by nlinarith [sq_nonneg (2 * x₁ + 1)]
      have hv : x₁ = 1 := by
        rcases mul_eq_zero.mp hx with h | h
        · linarith
        · linarith
      subst hv; norm_num
    -- Case 2: `(x₁, x₁, x₁, 2 - x₁)`.
    · have hx : (x₁ - 1) * (x₁ + 1) = 0 := by
        linear_combination (1/2 : ℝ) * h1 + (1/2 : ℝ) * h4
      rcases mul_eq_zero.mp hx with h | h
      · have hv : x₁ = 1 := by linarith
        subst hv; norm_num
      · have hv : x₁ = -1 := by linarith
        subst hv; norm_num
    -- Case 3: `(x₁, x₁, 2 - x₁, x₁)`.
    · have hx : (x₁ - 1) * (x₁ + 1) = 0 := by
        linear_combination (1/2 : ℝ) * h1 + (1/2 : ℝ) * h3
      rcases mul_eq_zero.mp hx with h | h
      · have hv : x₁ = 1 := by linarith
        subst hv; norm_num
      · have hv : x₁ = -1 := by linarith
        subst hv; norm_num
    -- Case 4: `(x₁, x₁, 2 - x₁, 2 - x₁)`.
    · have hx : (x₁ - 1) * (x₁ - 1) = 0 := by
        linear_combination (-1/2 : ℝ) * h1 + (-1/2 : ℝ) * h3
      have hv : x₁ = 1 := by
        rcases mul_eq_zero.mp hx with h | h <;> linarith
      subst hv; norm_num
    -- Case 5: `(x₁, 2 - x₁, x₁, x₁)`.
    · have hx : (x₁ - 1) * (x₁ + 1) = 0 := by
        linear_combination (1/2 : ℝ) * h1 + (1/2 : ℝ) * h2
      rcases mul_eq_zero.mp hx with h | h
      · have hv : x₁ = 1 := by linarith
        subst hv; norm_num
      · have hv : x₁ = -1 := by linarith
        subst hv; norm_num
    -- Case 6: `(x₁, 2 - x₁, x₁, 2 - x₁)`.
    · have hx : (x₁ - 1) * (x₁ - 1) = 0 := by
        linear_combination (-1/2 : ℝ) * h1 + (-1/2 : ℝ) * h2
      have hv : x₁ = 1 := by
        rcases mul_eq_zero.mp hx with h | h <;> linarith
      subst hv; norm_num
    -- Case 7: `(x₁, 2 - x₁, 2 - x₁, x₁)`.
    · have hx : (x₁ - 1) * (x₁ - 1) = 0 := by
        linear_combination (-1/2 : ℝ) * h1 + (-1/2 : ℝ) * h2
      have hv : x₁ = 1 := by
        rcases mul_eq_zero.mp hx with h | h <;> linarith
      subst hv; norm_num
    -- Case 8: `(x₁, 2 - x₁, 2 - x₁, 2 - x₁)`.
    · have hx : (x₁ - 1) * (x₁ - 3) = 0 := by
        linear_combination (1/2 : ℝ) * h1 + (1/2 : ℝ) * h2
      rcases mul_eq_zero.mp hx with h | h
      · have hv : x₁ = 1 := by linarith
        subst hv; norm_num
      · have hv : x₁ = 3 := by linarith
        subst hv; norm_num
  · rintro (⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩) <;> norm_num
