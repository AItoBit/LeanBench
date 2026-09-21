namespace IMO2018P3

open Finset

open scoped BigOperators

/-!
# IMO 2018 Problem 3 — arithmetic/counting core

The source introduces

    M n = maximum element in row n
    m n = minimum element in row n.

If the two numbers directly below `M n` are `a > b`,
then

    M n = a - b.

Since

    a ≤ M (n+1)
    m (n+1) ≤ b,

we get

    M n + m (n+1) ≤ M (n+1).

The final part of the source divides the integers into
"small" and "large" values and derives a counting
contradiction in the bottom row.

No `sorry`, `admit`, or extra axioms.
-/

/-!
## Triangular numbers
-/

def tri (n : ℕ) : ℕ :=
  n * (n + 1) / 2

def smallThreshold : ℕ :=
  tri 2017

def IsSmall (x : ℕ) : Prop :=
  x ≤ smallThreshold

def IsLarge (x : ℕ) : Prop :=
  smallThreshold < x
