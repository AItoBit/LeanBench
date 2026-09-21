/-- `cos (π/7)` is positive. -/
theorem cos_pi_div_seven_pos : 0 < Real.cos (π / 7) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · nlinarith [Real.pi_pos]
  · nlinarith [Real.pi_pos]

/-- `c = cos (π/7)` satisfies the cubic `8c³ - 4c² - 4c + 1 = 0`. -/
theorem cos_pi_div_seven_cubic :
    8 * Real.cos (π / 7) ^ 3 - 4 * Real.cos (π / 7) ^ 2 - 4 * Real.cos (π / 7) + 1 = 0 := by
  set c : ℝ := Real.cos (π / 7) with hc
  have hquart : Real.cos (4 * (π / 7)) = 8 * c ^ 4 - 8 * c ^ 2 + 1 := by
    have h : (4 : ℝ) * (π / 7) = 2 * (2 * (π / 7)) := by ring
    rw [h, Real.cos_two_mul, Real.cos_two_mul]
    ring
  have hcube : Real.cos (3 * (π / 7)) = 4 * c ^ 3 - 3 * c := by
    rw [Real.cos_three_mul]
  have hsum : Real.cos (4 * (π / 7)) = -Real.cos (3 * (π / 7)) := by
    have h : (4 : ℝ) * (π / 7) = π - 3 * (π / 7) := by ring
    rw [h, Real.cos_pi_sub]
  rw [hquart, hcube] at hsum
  have hne : c + 1 > 0 := by
    have := cos_pi_div_seven_pos
    rw [← hc] at this
    linarith
  have hfac : (c + 1) * (8 * c ^ 3 - 4 * c ^ 2 - 4 * c + 1) = 0 := by nlinarith [hsum]
  rcases mul_eq_zero.mp hfac with h | h
  · linarith
  · exact h
