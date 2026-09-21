/--
The product of the three ratios appearing after the
angle-bisector reduction.
-/
theorem candidate
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (hA : a < b + c)
    (hB : b < c + a)
    (hC : c < a + b) :
    (1 : ℝ) / 4 <
        ((b + c) / (a + b + c)) *
        ((c + a) / (a + b + c)) *
        ((a + b) / (a + b + c)) ∧
      ((b + c) / (a + b + c)) *
        ((c + a) / (a + b + c)) *
        ((a + b) / (a + b + c)) ≤
          (8 : ℝ) / 27 :=
