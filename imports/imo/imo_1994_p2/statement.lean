/--
IMO 1994 Problem 2.
We set the origin at M, the midpoint of BC.
A = (0, a), B = (-b, 0), C = (b, 0), O = (0, y_o), Q = (q, 0).
E is parametrized along AB by `s`, and F is parametrized along AC by `t`.
-/
theorem candidate (a b q s t y_o : ℝ)
  (ha : a ≠ 0) (hb : b ≠ 0)
  (hs : s ≠ 1) (ht : t ≠ 1)
  (hDE : (-b*(1-s) - q)^2 + (a*s)^2 ≠ 0)
  (h_yo : b^2 + a*y_o = 0)
  (h_cross : (-b*(1-s) - q) * (a*t) - (a*s) * (b*(1-t) - q) = 0) :
  ((-b*(1-s) - q)^2 + (a*s)^2 = (b*(1-t) - q)^2 + (a*t)^2) ↔
  ((b*(1-t) + b*(1-s)) * q - a*(t-s)*y_o = 0) :=
