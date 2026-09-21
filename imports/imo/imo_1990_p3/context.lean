open scoped BigOperators

open scoped Real

open scoped Nat

open scoped Classical

open scoped Pointwise

set_option maxHeartbeats 8000000

set_option maxRecDepth 4000

set_option synthInstance.maxHeartbeats 20000

set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false

set_option autoImplicit false

set_option grind.warning false

/-!
# IMO 1990 Problem 3

Determine all integers `n > 1` such that `(2 ^ n + 1) / n ^ 2` is an integer.

The answer is `n = 3`.
-/

namespace Imo1990P3
