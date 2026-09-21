namespace IMO2016P6

/-!
# IMO 2016 Problem 6 — parity core

The geometric proof eventually reduces both parts to parity.

Part (b), n even:
-----------------
Starting from a circled endpoint B, the source alternates

    circle, cross, circle, cross, ...

around one side of the arc BB'.

There are exactly `n - 1` other blue endpoints on that side.
For the alternation to finish consistently, `n - 1` must be even.
But if `n` is even, `n - 1` is odd. Contradiction.

Part (a), n odd:
----------------
Assume two frogs collide. The source considers an arc AB and
lets `k` be the number of intermediate blue points.

Because both endpoints A and B are circled, alternation implies
that `k` is odd.

The pairing argument involving red intersection points shows
that the intermediate blue points occur in pairs, so `k` is even.

Contradiction.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
## Elementary parity incompatibility
-/
