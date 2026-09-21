by
  have h_sin_sub : sin (x₂ - x₁) = sin x₂ * cos x₁ - cos x₂ * sin x₁ := sin_sub x₂ x₁
  
  -- We expand the product (A^2 + B^2) * sin(x₂ - x₁) to show it factors 
  -- perfectly into the root equations.
  have h_expand : (A^2 + B^2) * sin (x₂ - x₁) =
    (A * sin x₂ + B * cos x₂) * (A * cos x₁ - B * sin x₁) -
    (A * sin x₁ + B * cos x₁) * (A * cos x₂ - B * sin x₂) := by
    calc (A^2 + B^2) * sin (x₂ - x₁)
      _ = (A^2 + B^2) * (sin x₂ * cos x₁ - cos x₂ * sin x₁) := by rw [h_sin_sub]
      _ = (A * sin x₂ + B * cos x₂) * (A * cos x₁ - B * sin x₁) -
          (A * sin x₁ + B * cos x₁) * (A * cos x₂ - B * sin x₂) := by ring
          
  -- Substitute the root conditions to show the entire expression vanishes
  have h_zero : (A^2 + B^2) * sin (x₂ - x₁) = 0 := by
    calc (A^2 + B^2) * sin (x₂ - x₁)
      _ = (A * sin x₂ + B * cos x₂) * (A * cos x₁ - B * sin x₁) -
          (A * sin x₁ + B * cos x₁) * (A * cos x₂ - B * sin x₂) := h_expand
      _ = (A * sin x₂ + B * cos x₂) * 0 - (A * sin x₁ + B * cos x₁) * 0 := by rw [hx₁, hx₂]
      _ = 0 := by ring
      
  -- Since A^2 + B^2 > 0, it must be that sin(x₂ - x₁) is exactly 0
  have h_pos : A^2 + B^2 ≠ 0 := by linarith
  
  cases mul_eq_zero.mp h_zero with
  | inl h => exact False.elim (h_pos h)
  | inr h => exact h
