namespace IMO1984P6

theorem candidate
  (a b P_m1 P_km1 : ℤ)
  (h_prod : (b - a) * (b + a) = b * (2 * P_m1) - a * (P_m1 * P_km1))
  (h_sum : b + a = P_m1)
  (h_Pm1_pos : P_m1 ≠ 0) :
  a * P_km1 = P_m1 :=
