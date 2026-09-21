open scoped BigOperators

open scoped Real

open scoped Nat

open scoped Pointwise

set_option maxHeartbeats 8000000

set_option maxRecDepth 4000

set_option relaxedAutoImplicit false

set_option autoImplicit false

/-!
# IMO 1961 Problem 1

Solve the following equations for `x, y, z`:
`x + y + z = a`, `x^2 + y^2 + z^2 = b^2`, `x * y = z^2`.
What conditions must `a` and `b` satisfy for `x, y, z` to be distinct positive numbers?

The answer is `a > 0` together with `b^2 < a^2 < 3 * b^2`.

The originally proposed formalization omitted the condition `a > 0`; that version of the
statement is false (see `imo_1961_p1_without_pos_false` below), so the corrected statement
`imo_1961_p1` includes `0 < a` in the answer.
-/
