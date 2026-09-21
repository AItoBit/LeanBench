namespace IMO2016P2

/-!
# IMO 2016 Problem 2 — counting/divisibility core

The source first observes that `3 ∣ n`, so write

    n = 3k.

The double-counting argument then gives

    total number of I-cells
      = 4k² - 3a,

while the row condition gives

    total number of I-cells
      = 3k².

Hence

    4k² - 3a = 3k²,

so

    k² = 3a.

Therefore `3 ∣ k²`. Since `3` is prime, `3 ∣ k`,
and consequently

    9 ∣ n.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
## Algebraic form of the double count
-/
