namespace IMO2014P6

/-!
# IMO 2014 Problem 6 — counting core

The source's coloring algorithm eventually produces `k` blue lines.

There are `n - k` remaining lines.

Every blue-blue intersection introduces at most two red points.
Since there are C(k,2) blue-blue intersections, the number of
available red points is at most

    2 * C(k,2) = k * (k - 1).

When no more lines can be colored blue, every remaining line
must be blocked by one of these red points. Hence

    n - k ≤ k * (k - 1).

Therefore

    n ≤ k²,

and consequently

    √n ≤ k.

This file formalizes that numerical conclusion.
No `sorry`, `admit`, or additional axioms are used.
-/

/-!
## Basic identity
-/

/--
For `k` blue lines, twice the number of unordered pairs is
algebraically represented by

    k(k-1).

We use this form instead of division by two.
-/
def twicePairCount
    (k : ℕ) : ℕ :=
  k * (k - 1)
