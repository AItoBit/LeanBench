namespace IMO2019P1

/-!
# IMO 2019 Problem 1

Determine all functions `f : ℤ → ℤ` satisfying

    f (2 * a) + 2 * f b = f (f (a + b))

for all integers `a, b`.

The solutions are exactly

    f x = 0

and

    f x = 2 * x + c

for arbitrary `c : ℤ`.

No `sorry`, `admit`, or additional axioms.
-/

/-!
============================================================
1. Functional equation
============================================================
-/

def FunctionalEquation
    (f : ℤ → ℤ) : Prop :=
  ∀ a b : ℤ,
    f (2 * a) + 2 * f b =
      f (f (a + b))

/-!
============================================================
2. Doubling identity
============================================================
-/
