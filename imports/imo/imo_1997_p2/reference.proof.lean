by
  -- `sin(2u+2A) = sin A cos(2u+A) + cos A sin(2u+A)`
  have i1 : Real.sin (2 * u + 2 * A)
      = Real.sin A * Real.cos (2 * u + A) + Real.cos A * Real.sin (2 * u + A) := by
    have h := Real.sin_add A (2 * u + A)
    rw [show A + (2 * u + A) = 2 * u + 2 * A by ring] at h
    exact h
  -- `sin(2u+2A) = 2 sin(u+A) cos(u+A)`
  have i2 : Real.sin (2 * u + 2 * A) = 2 * Real.sin (u + A) * Real.cos (u + A) := by
    rw [show 2 * u + 2 * A = 2 * (u + A) by ring, Real.sin_two_mul]
  -- `sin(2u+A) + sin A = 2 sin(u+A) cos u`
  have i3 : Real.sin (2 * u + A) + Real.sin A = 2 * Real.sin (u + A) * Real.cos u := by
    have e1 : Real.sin (u + A) * Real.cos u + Real.cos (u + A) * Real.sin u
        = Real.sin (2 * u + A) := by
      rw [← Real.sin_add, show (u + A) + u = 2 * u + A by ring]
    have e2 : Real.sin (u + A) * Real.cos u - Real.cos (u + A) * Real.sin u = Real.sin A := by
      rw [← Real.sin_sub, show (u + A) - u = A by ring]
    linear_combination -e1 - e2
  -- eliminate `TB`, then `TC`
  have ha : TC * Real.sin (2 * u + 2 * A) = BC * Real.sin (2 * u + A) := by
    linear_combination Real.sin (2 * u + A) * h3 - Real.cos (2 * u + A) * h4 + TC * i1
  have hb : TB * Real.sin (2 * u + 2 * A) = BC * Real.sin A := by
    linear_combination Real.sin A * h3 + Real.cos A * h4 + TB * i1
  have hc : (TB + TC) * Real.sin (2 * u + 2 * A)
      = BC * (Real.sin (2 * u + A) + Real.sin A) := by
    linear_combination ha + hb
  rw [i2, i3] at hc
  -- cancel `2 sin(u+A)`
  have h2P : (2 : ℝ) * Real.sin (u + A) ≠ 0 := by
    simpa using hP
  have hc' : (2 * Real.sin (u + A)) * ((TB + TC) * Real.cos (u + A))
      = (2 * Real.sin (u + A)) * (BC * Real.cos u) := by linear_combination hc
  have hd := mul_left_cancel₀ h2P hc'
  -- cancel `cos(u+A)`
  rw [hBC] at hd
  have he : Real.cos (u + A) * (TB + TC) = Real.cos (u + A) * (2 * R * Real.cos u) := by
    linear_combination hd
  have hfin := mul_left_cancel₀ hQ he
  rw [hAU]
  linarith [hfin]
