by
  
  -- Express the ratio A_{n-1} / A_n as 1 - (x_n * a^n) / A_n
  have hA_div : A_prev / An = 1 - xn_an / An := by
    have h_sub : A_prev = An - xn_an := by linarith [hA]
    calc A_prev / An
      _ = (An - xn_an) / An := by rw [h_sub]
      _ = An / An - xn_an / An := sub_div An xn_an An
      _ = 1 - xn_an / An := by rw [div_self hAn_ne]
      
  -- Express the ratio B_{n-1} / B_n as 1 - (x_n * b^n) / B_n
  have hB_div : B_prev / Bn = 1 - xn_bn / Bn := by
    have h_sub : B_prev = Bn - xn_bn := by linarith [hB]
    calc B_prev / Bn
      _ = (Bn - xn_bn) / Bn := by rw [h_sub]
      _ = Bn / Bn - xn_bn / Bn := sub_div Bn xn_bn Bn
      _ = 1 - xn_bn / Bn := by rw [div_self hBn_ne]
      
  -- Substitute the simplified forms and apply the given inequality
  rw [hA_div, hB_div]
  linarith
