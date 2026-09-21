by
  constructor
  
  -- Forward Direction: QE = QF ⟹ OQ ⟂ EF
  · intro h_dist
    have h_DistDiff : (-b*(1-s) - q)^2 + (a*s)^2 - ((b*(1-t) - q)^2 + (a*t)^2) = 0 := sub_eq_zero.mpr h_dist
    have H : 2 * ((-b*(1-s) - q)^2 + (a*s)^2) * a^2 * ((b*(1-t) + b*(1-s)) * q - a*(t-s)*y_o) = 0 := by
      calc 2 * ((-b*(1-s) - q)^2 + (a*s)^2) * a^2 * ((b*(1-t) + b*(1-s)) * q - a*(t-s)*y_o)
        _ = ((-b*(1-s) - q)^2 + (a*s)^2 - ((b*(1-t) - q)^2 + (a*t)^2)) *
              ( ((-b*(1-s) - q)^2 + (a*s)^2) * a^2 - a^2 * s^2 * (a^2 + b^2) )
            + ((-b*(1-s) - q) * (a*t) - (a*s) * (b*(1-t) - q)) *
              ((-b*(1-s) - q) * (a*t) + (a*s) * (b*(1-t) - q)) * (a^2 + b^2)
            - 2 * ((-b*(1-s) - q)^2 + (a*s)^2) * a^2 * (t-s) * (b^2 + a*y_o) := imo1994_p2_id_fwd a b q s t y_o
        _ = 0 * ( ((-b*(1-s) - q)^2 + (a*s)^2) * a^2 - a^2 * s^2 * (a^2 + b^2) )
            + 0 * ((-b*(1-s) - q) * (a*t) + (a*s) * (b*(1-t) - q)) * (a^2 + b^2)
            - 2 * ((-b*(1-s) - q)^2 + (a*s)^2) * a^2 * (t-s) * 0 := by rw [h_DistDiff, h_cross, h_yo]
        _ = 0 := by ring
    
    cases mul_eq_zero.mp H with
    | inl h1 =>
      cases mul_eq_zero.mp h1 with
      | inl h3 =>
        cases mul_eq_zero.mp h3 with
        | inl h4 => norm_num at h4
        | inr h4 => exact False.elim (hDE h4)
      | inr h3 =>
        have ha2 : a * a = 0 := by
          calc a * a = a^2 := by ring
            _ = 0 := h3
        cases mul_eq_zero.mp ha2 with
        | inl h4 => exact False.elim (ha h4)
        | inr h4 => exact False.elim (ha h4)
    | inr h1 => exact h1
  
  -- Backward Direction: OQ ⟂ EF ⟹ QE = QF
  · intro h_dot
    have H : (2 * a * b^2 * (1-s) * (1-t)) * ((-b*(1-s) - q)^2 + (a*s)^2 - ((b*(1-t) - q)^2 + (a*t)^2)) = 0 := by
      calc (2 * a * b^2 * (1-s) * (1-t)) * ((-b*(1-s) - q)^2 + (a*s)^2 - ((b*(1-t) - q)^2 + (a*t)^2))
        _ = ((b*(1-t) + b*(1-s)) * q - a*(t-s)*y_o) *
              ( a * (s-t)^2 * (a^2+b^2) + 2 * (2 * a * b^2 * (1-s) * (1-t)) )
            - ((-b*(1-s) - q) * (a*t) - (a*s) * (b*(1-t) - q)) *
              ( b * (2-s-t) * (s-t) * (a^2+b^2) )
            + (b^2 + a*y_o) *
              ( 2 * (2 * a * b^2 * (1-s) * (1-t)) * (t-s) - a * (s-t)^3 * (a^2+b^2) ) := imo1994_p2_id_bwd a b q s t y_o
        _ = 0 * ( a * (s-t)^2 * (a^2+b^2) + 2 * (2 * a * b^2 * (1-s) * (1-t)) )
            - 0 * ( b * (2-s-t) * (s-t) * (a^2+b^2) )
            + 0 * ( 2 * (2 * a * b^2 * (1-s) * (1-t)) * (t-s) - a * (s-t)^3 * (a^2+b^2) ) := by rw [h_dot, h_cross, h_yo]
        _ = 0 := by ring
    
    have hW : 2 * a * b^2 * (1 - s) * (1 - t) ≠ 0 := by
      have h2 : (2 : ℝ) ≠ 0 := by norm_num
      have hb2 : b^2 ≠ 0 := by
        intro h
        have hb_mul : b * b = 0 := by
          calc b * b = b^2 := by ring
            _ = 0 := h
        cases mul_eq_zero.mp hb_mul with
        | inl h1 => exact hb h1
        | inr h1 => exact hb h1
      have hs1 : 1 - s ≠ 0 := sub_ne_zero.mpr hs.symm
      have ht1 : 1 - t ≠ 0 := sub_ne_zero.mpr ht.symm
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h2 ha) hb2) hs1) ht1
      
    cases mul_eq_zero.mp H with
    | inl h1 => exact False.elim (hW h1)
    | inr h1 => exact sub_eq_zero.mp h1
