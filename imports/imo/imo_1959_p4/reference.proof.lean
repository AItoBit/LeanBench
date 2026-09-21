by
  let a := (c / 4) * (Real.sqrt 6 + Real.sqrt 2)
  let b := (c / 4) * (Real.sqrt 6 - Real.sqrt 2)
  use a, b

  have h6_pos : (0 : ℝ) < 6 := by norm_num
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  have h6_ge : (0 : ℝ) ≤ 6 := by norm_num
  have h2_ge : (0 : ℝ) ≤ 2 := by norm_num

  have h_sqrt6_sq : (Real.sqrt 6)^2 = 6 := Real.sq_sqrt h6_ge
  have h_sqrt2_sq : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt h2_ge

  have h_lt : Real.sqrt 2 < Real.sqrt 6 := Real.sqrt_lt_sqrt h2_ge (by norm_num)

  have ha_pos : 0 < a := by
    have h_sum : 0 < Real.sqrt 6 + Real.sqrt 2 := by positivity
    exact mul_pos (by linarith) h_sum

  have hb_pos : 0 < b := by
    have h_diff : 0 < Real.sqrt 6 - Real.sqrt 2 := sub_pos.mpr h_lt
    exact mul_pos (by linarith) h_diff

  have h_prod : a * b = (c / 2)^2 := by
    calc
      a * b = ((c / 4) * (c / 4)) * ((Real.sqrt 6 + Real.sqrt 2) * (Real.sqrt 6 - Real.sqrt 2)) := by ring
      _ = (c^2 / 16) * ((Real.sqrt 6)^2 - (Real.sqrt 2)^2) := by ring
      _ = (c^2 / 16) * (6 - 2) := by rw [h_sqrt6_sq, h_sqrt2_sq]
      _ = c^2 / 4 := by ring
      _ = (c / 2)^2 := by ring

  have h_pyth : a^2 + b^2 = c^2 := by
    calc
      a^2 + b^2 = (c / 4)^2 * ((Real.sqrt 6 + Real.sqrt 2)^2 + (Real.sqrt 6 - Real.sqrt 2)^2) := by ring
      _ = (c^2 / 16) * (2 * (Real.sqrt 6)^2 + 2 * (Real.sqrt 2)^2) := by ring
      _ = (c^2 / 16) * (2 * 6 + 2 * 2) := by rw [h_sqrt6_sq, h_sqrt2_sq]
      _ = (c^2 / 16) * 16 := by ring
      _ = c^2 := by ring

  refine ⟨ha_pos, hb_pos, h_pyth, h_prod.symm⟩
