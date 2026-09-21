/-- The core algebraic identity from the solution, formulated over ℤ. -/
lemma identity (a b : ℤ) :
    (a + b)^7 - a^7 - b^7 = 7 * a * b * (a + b) * (a^2 + a * b + b^2)^2 := by
  ring
