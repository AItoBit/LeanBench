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

set_option pp.fullNames true

set_option pp.structureInstances true

set_option pp.coercions.types true

set_option pp.funBinderTypes true

set_option pp.letVarTypes true

set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# IMO 2000 Problem 5

Does there exist a positive integer `n` such that `n` has exactly 2000 prime divisors
and `n` divides `2 ^ n + 1`?  The answer is **yes**.

We prove the more general statement that for every `k` there is a positive integer `n`
divisible by `3`, with exactly `k + 1` distinct prime divisors, such that `n ∣ 2 ^ n + 1`.
-/

namespace Imo2000P5
