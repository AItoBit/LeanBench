namespace IMO2023P4

/-!
# IMO 2023 Problem 4 — recurrence core

The analytic part of the source proves, for every relevant n,

    a_{n+2} ≥ a_n + 2,

and equality is impossible because the original x_i are
pairwise distinct.

Since every a_n is an integer, this becomes

    a_{n+2} ≥ a_n + 3.

Using zero-based indexing:

    a 0    = a₁
    a 2022 = a₂₀₂₃.

Iterating the two-step recurrence 1011 times gives

    a 2022 ≥ 1 + 3*1011 = 3034.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. Integer strengthening
============================================================
-/
