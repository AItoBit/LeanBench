namespace IMO2015P5

/-!
# IMO 2015 Problem 5

Determine all functions `f : ℝ → ℝ` satisfying

    f (x + f (x + y)) + f (x * y)
      =
    x + f (x + y) + y * f x

for all real `x,y`.

The solutions are

    f x = x

and

    f x = 2 - x.

No `sorry`, `admit`, or extra axioms are used.
-/

/-!
## Functional equation
-/

def FunctionalEquation (f : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ,
    f (x + f (x + y)) + f (x * y)
      =
    x + f (x + y) + y * f x

/-!
## Verification of the two solutions
-/
