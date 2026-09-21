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
# IMO 1981 Problem 4

(a) For which values of `n > 2` is there a set of `n` consecutive positive integers such that the
largest number in the set is a divisor of the least common multiple of the remaining `n - 1`
numbers?  Answer: exactly the `n` with `n ≥ 4`.

(b) For which values of `n > 2` is there exactly one such set?  Answer: only `n = 4`
(the set `{3, 4, 5, 6}`).
-/

namespace IMO1981P4

/-- `ConsecLcmProp n m` says that the set of `n` consecutive positive integers
`{m, m+1, ..., m+n-1}` has the property that its largest element `m + n - 1` divides the least
common multiple of the other `n - 1` elements. -/
def ConsecLcmProp (n m : ℕ) : Prop :=
  0 < m ∧ (m + n - 1) ∣ (Finset.range (n - 1)).lcm (fun i => m + i)
