namespace IMO2018P5

/-!
# IMO 2018 Problem 5 — stabilization core

The source's p-adic argument eventually proves that for all
sufficiently large `n`,

    a (n + 1) ∣ a n.

Because all `a n` are positive, this implies

    a (n + 1) ≤ a n.

Thus the tail is a nonincreasing sequence of positive
natural numbers and must eventually stabilize.

This file formalizes that final descent argument and the
finite synchronization step used in the p-adic proof.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. Positivity plus divisibility gives an inequality
============================================================
-/
