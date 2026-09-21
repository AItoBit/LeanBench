namespace IMO1984P5

/-- The upper bound expression from the problem, using integer division. -/
def upperBound (n : ℤ) : ℤ :=
  (n / 2) * ((n + 1) / 2) - 2
