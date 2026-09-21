theorem candidate
    {a b c d : ℝ}
    (hab : b ≤ a)
    (hbc : c ≤ b)
    (hcd : d ≤ c)
    (hd : 0 < d)
    (hsum :
      a + b + c + d = 1) :
    (a + 2 * b + 3 * c + 4 * d) *
        (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)
      <
    1 :=
