/--
IMO 2019 Problem 1.

    FunctionalEquation f

holds if and only if either

    f(x)=0

for every integer `x`, or there is `c : ℤ` such that

    f(x)=2x+c

for every integer `x`.
-/
theorem candidate
    (f : ℤ → ℤ) :
    FunctionalEquation f
      ↔
    ((∀ x : ℤ,
        f x = 0)
      ∨
      (∃ c : ℤ,
        ∀ x : ℤ,
          f x =
            2 * x + c)) :=
