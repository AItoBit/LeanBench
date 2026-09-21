/-- IMO 1959 Problem 1: the fraction `(21n+4)/(14n+3)` is irreducible for every
natural number `n`, i.e. its numerator and denominator are coprime.

The hypothesis `0 < n` is part of the original statement; it turned out to be
unnecessary, as the result holds for every natural number `n`. -/
theorem candidate (n : ℕ) (_h₀ : 0 < n) : Nat.gcd (21 * n + 4) (14 * n + 3) = 1 :=
