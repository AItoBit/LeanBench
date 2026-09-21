namespace IMO2022P2

/-!
# IMO 2022 Problem 2

Let f : ℝ₊ → ℝ₊ satisfy:

for every positive x there is exactly one positive y such that

    x * f y + y * f x ≤ 2.

Then

    f x = 1 / x

for every positive x.

We work with ordinary real numbers and carry positivity
explicitly in the hypotheses.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. The relation from the problem
============================================================
-/

def Good
    (f : ℝ → ℝ)
    (x y : ℝ) : Prop :=
  0 < y ∧
  x * f y + y * f x ≤ 2

/-!
The relation is symmetric on positive x,y.
-/
