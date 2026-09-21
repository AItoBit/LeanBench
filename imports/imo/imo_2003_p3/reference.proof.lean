by
  -- Step 1: Derive the relation between the squares of the sides
  have h1 : a^2 + b^2 = 2 * c^2 := by linarith
  have h2 : b^2 + c^2 = 2 * a^2 := by linarith
  have h3 : c^2 + a^2 = 2 * b^2 := by linarith
  
  -- Step 2: Show the squares are equal
  have hab_sq : a^2 = b^2 := by linarith
  have hbc_sq : b^2 = c^2 := by linarith
  
  -- Step 3: Prove a = b from a^2 = b^2 and non-negativity
  have hab : a = b := by
    have h_mul : (a - b) * (a + b) = 0 := by
      calc (a - b) * (a + b) = a^2 - b^2 := by ring
      _ = 0 := by linarith
    cases mul_eq_zero.mp h_mul with
    | inl h_minus => linarith
    | inr h_plus => 
      have ha_zero : a = 0 := by linarith
      have hb_zero : b = 0 := by linarith
      linarith

  -- Step 4: Prove b = c from b^2 = c^2 and non-negativity
  have hbc : b = c := by
    have h_mul : (b - c) * (b + c) = 0 := by
      calc (b - c) * (b + c) = b^2 - c^2 := by ring
      _ = 0 := by linarith
    cases mul_eq_zero.mp h_mul with
    | inl h_minus => linarith
    | inr h_plus => 
      have hb_zero : b = 0 := by linarith
      have hc_zero : c = 0 := by linarith
      linarith

  -- Conclude the triangle is equilateral
  exact ⟨hab, hbc⟩
