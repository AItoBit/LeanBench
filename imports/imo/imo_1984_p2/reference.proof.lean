by
  -- As found in the text, we use a = 18 and b = 1
  use 18, 1
  refine ⟨by decide, by decide, by decide, ?_⟩
  
  -- Apply the binomial expansion identity
  rw [identity]
  
  -- Substitute the inner quadratic factor with 7^3
  have h_square : (18 : ℤ)^2 + 18 * 1 + 1^2 = 7^3 := by decide
  rw [h_square]
  
  -- Rearrange the powers of 7 to explicitly show 7^7 as a factor
  have h_factor : 7 * 18 * 1 * (18 + 1) * ((7 : ℤ)^3)^2 = 7^7 * (18 * 1 * (18 + 1)) := by ring
  rw [h_factor]
  
  exact dvd_mul_right (7^7) (18 * 1 * (18 + 1))
