/--
Thus after sorting the variables, the three powers of two occur
in nondecreasing order, exactly as in the source proof.
-/
theorem candidate
    {a b c : ℤ}
    (hgood : Good a b c)
    (hab : a ≤ b)
    (hbc : b ≤ c) :
    a * b - c ≤
      c * a - b ∧
    c * a - b ≤
      b * c - a :=
