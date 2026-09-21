theorem candidate (a b c : ℤ) (h1 : 1 < a) (hab : a < b) (hbc : b < c) :
    ((a - 1) * (b - 1) * (c - 1) ∣ a * b * c - 1) ↔
      (a = 2 ∧ b = 4 ∧ c = 8) ∨ (a = 3 ∧ b = 5 ∧ c = 15) :=
