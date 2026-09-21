namespace IMO1984B2

theorem candidate
  (x k1 k2 r s3 : ℝ)
  (hs3 : s3 ≠ 0)
  (hM_x : k1 + (1 - k1) * x = 3 * r / 2)
  (hM_y : k1 * s3 = (1 - r) * s3 + r * s3 / 2)
  (hN_x : k2 + (1 - k2) * x = 3 * (1 - r) / 2)
  (hN_y : k2 * s3 = (1 - r) * s3 / 2) :
  r^2 = 1 / 3 :=
