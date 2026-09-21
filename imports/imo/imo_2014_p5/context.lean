namespace IMO2014P5

open Finset

open scoped BigOperators

/-!
# IMO 2014 Problem 5 — final packing core

The official proof eventually reduces to the following argument.

There are `k` boxes, each of capacity `1`.
Every remaining light coin has value at most

    1 / (2k + 1).

If a light coin remains and cannot be placed in any box,
then every box has weight greater than

    1 - 1 / (2k + 1).

For `k = 100`, this forces the total weight to be greater than

    100 * (1 - 1 / 201)

which is greater than

    99 + 1/2.

This contradicts the total-value bound.

No `sorry`, `admit`, or extra axioms are used.
-/

/-!
## Summing strict lower bounds
-/

noncomputable def lightThreshold
    (k : ℕ) : ℝ :=
  1 / ((2 * k + 1 : ℕ) : ℝ)
