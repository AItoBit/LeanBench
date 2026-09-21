/-- IMO 2002, Problem 3, with the quotient explicitly required to be an integer.
Both directions are proved: necessity and infinitely many positive witnesses for (5, 3). -/
theorem candidate (m n : ℕ) (hm : 3 ≤ m) (hn : 3 ≤ n) :
    Set.Infinite {a : ℤ | 0 < a ∧ ∃ z : ℤ,
      ((a : ℚ) ^ m + a - 1) / ((a : ℚ) ^ n + a ^ 2 - 1) = z} ↔
      m = 5 ∧ n = 3 :=
