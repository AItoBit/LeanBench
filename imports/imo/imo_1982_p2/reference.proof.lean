by
  have hu10 : u₁ ≠ 0 := by intro h; rw [h] at hu₁; simp at hu₁
  have hu20 : u₂ ≠ 0 := by intro h; rw [h] at hu₂; simp at hu₂
  have hu30 : u₃ ≠ 0 := by intro h; rw [h] at hu₃; simp at hu₃
  have c1 : (starRingEnd ℂ) u₁ = 1 / u₁ := by field_simp; linear_combination hu₁
  have c2 : (starRingEnd ℂ) u₂ = 1 / u₂ := by field_simp; linear_combination hu₂
  have c3 : (starRingEnd ℂ) u₃ = 1 / u₃ := by field_simp; linear_combination hu₃
  have hne12 : (u₁ + u₂ + u₃) * (u₁ * u₂ + u₂ * u₃ + u₃ * u₁) ≠ 0 := mul_ne_zero he1 he2
  -- conjugation of the elementary symmetric functions, stated multiplicatively
  have ce1 : (starRingEnd ℂ) (u₁ + u₂ + u₃) * (u₁ * u₂ * u₃)
      = u₁ * u₂ + u₂ * u₃ + u₃ * u₁ := by
    rw [map_add, map_add, c1, c2, c3]
    field_simp
    ring
  have ce2 : (starRingEnd ℂ) (u₁ * u₂ + u₂ * u₃ + u₃ * u₁) * (u₁ * u₂ * u₃)
      = u₁ + u₂ + u₃ := by
    rw [map_add, map_add, map_mul, map_mul, map_mul, c1, c2, c3]
    field_simp
    ring
  have ce3 : (starRingEnd ℂ) (u₁ * u₂ * u₃) * (u₁ * u₂ * u₃) = 1 := by
    rw [map_mul, map_mul, c1, c2, c3]
    field_simp
  have hcE1 : (starRingEnd ℂ) (u₁ + u₂ + u₃) ≠ 0 := by
    intro h
    rw [h, zero_mul] at ce1
    exact he2 ce1.symm
  have hcE2 : (starRingEnd ℂ) (u₁ * u₂ + u₂ * u₃ + u₃ * u₁) ≠ 0 := by
    intro h
    rw [h, zero_mul] at ce2
    exact he1 ce2.symm
  subst hA₁; subst hA₂; subst hA₃; subst hS₁; subst hS₂; subst hS₃
  subst hM₁; subst hM₂; subst hM₃
  refine ⟨(u₁ * u₂ + u₂ * u₃ + u₃ * u₁) / (u₁ + u₂ + u₃),
    u₁ * u₂ * u₃ / ((u₁ + u₂ + u₃) * (u₁ * u₂ + u₂ * u₃ + u₃ * u₁)), ?_, ?_, ?_, ?_⟩
  · -- `λ` is real
    rw [map_div₀, map_mul, div_eq_div_iff (mul_ne_zero hcE1 hcE2) hne12]
    linear_combination
      ((starRingEnd ℂ) (u₁ + u₂ + u₃) * (starRingEnd ℂ) (u₁ * u₂ + u₂ * u₃ + u₃ * u₁) *
          (u₁ * u₂ * u₃)) * ce3
      - ((starRingEnd ℂ) (u₁ + u₂ + u₃) * (starRingEnd ℂ) (u₁ * u₂ * u₃) *
          (u₁ * u₂ * u₃)) * ce2
      - ((starRingEnd ℂ) (u₁ * u₂ * u₃) * (u₁ + u₂ + u₃)) * ce1
  · have h1 : (u₁ * u₂ + u₂ * u₃ + u₃ * u₁) / (u₁ + u₂ + u₃)
        - (2 * u₃ * u₁ / (u₃ + u₁) + 2 * u₁ * u₂ / (u₁ + u₂)) / 2
        = (u₁ * u₂ * u₃ * (u₂ * u₃ / u₁
            - (2 * u₃ * u₁ / (u₃ + u₁) + 2 * u₁ * u₂ / (u₁ + u₂)) / 2))
          / ((u₁ + u₂ + u₃) * (u₁ * u₂ + u₂ * u₃ + u₃ * u₁)) := by
      rw [eq_div_iff hne12]
      field_simp
      ring
    rw [div_mul_eq_mul_div]
    linear_combination h1
  · have h1 : (u₁ * u₂ + u₂ * u₃ + u₃ * u₁) / (u₁ + u₂ + u₃)
        - (2 * u₁ * u₂ / (u₁ + u₂) + 2 * u₂ * u₃ / (u₂ + u₃)) / 2
        = (u₁ * u₂ * u₃ * (u₃ * u₁ / u₂
            - (2 * u₁ * u₂ / (u₁ + u₂) + 2 * u₂ * u₃ / (u₂ + u₃)) / 2))
          / ((u₁ + u₂ + u₃) * (u₁ * u₂ + u₂ * u₃ + u₃ * u₁)) := by
      rw [eq_div_iff hne12]
      field_simp
      ring
    rw [div_mul_eq_mul_div]
    linear_combination h1
  · have h1 : (u₁ * u₂ + u₂ * u₃ + u₃ * u₁) / (u₁ + u₂ + u₃)
        - (2 * u₂ * u₃ / (u₂ + u₃) + 2 * u₃ * u₁ / (u₃ + u₁)) / 2
        = (u₁ * u₂ * u₃ * (u₁ * u₂ / u₃
            - (2 * u₂ * u₃ / (u₂ + u₃) + 2 * u₃ * u₁ / (u₃ + u₁)) / 2))
          / ((u₁ + u₂ + u₃) * (u₁ * u₂ + u₂ * u₃ + u₃ * u₁)) := by
      rw [eq_div_iff hne12]
      field_simp
      ring
    rw [div_mul_eq_mul_div]
    linear_combination h1
