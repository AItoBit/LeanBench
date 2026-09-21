namespace IMO2014P2

/-!
IMO 2014 Problem 2 — arithmetic/counting core.

The official solution sets

    k = ⌈√n⌉ - 1.

Writing q = k + 1 = ⌈√n⌉, we have

    (q - 1)^2 < n ≤ q^2.

Hence

    k^2 < n

and consequently

    n - k + 1 > k(k - 1) + 1.

This is the key numerical inequality in the pigeonhole
argument from the official solution.
-/

/-!
## Elementary arithmetic
-/
