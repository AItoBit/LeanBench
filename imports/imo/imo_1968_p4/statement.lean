theorem candidate
  (a b c d e f : ℝ)
  (face1 : a + b > c ∧ b + c > a ∧ c + a > b)
  (face2 : a + e > f ∧ e + f > a ∧ f + a > e)
  (face3 : b + d > f ∧ d + f > b ∧ f + b > d)
  (_face4 : c + d > e ∧ d + e > c ∧ e + c > d)
  (hmax_b : a ≥ b)
  (_hmax_c : a ≥ c)
  (hmax_d : a ≥ d)
  (_hmax_e : a ≥ e)
  (_hmax_f : a ≥ f) :
  (b + c > d ∧ c + d > b ∧ d + b > c) ∨
  (a + c > e ∧ c + e > a ∧ e + a > c) ∨
  (a + b > f ∧ b + f > a ∧ f + a > b) ∨
  (d + e > f ∧ e + f > d ∧ f + d > e) :=
