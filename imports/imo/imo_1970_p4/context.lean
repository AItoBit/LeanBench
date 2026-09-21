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
## IMO 1970, Problem 4

Find the set of all positive integers `n` with the property that the set
`{n, n+1, n+2, n+3, n+4, n+5}` can be partitioned into two sets such that the
product of the numbers in one set equals the product of the numbers in the
other set.

The answer is that **there is no such `n`**: the set of such `n` is empty.

A partition of the block into two parts is recorded by one part `A`; the other
part is then `block n \ A`.
-/

namespace IMO1970P4

/-- The block `{n, n+1, n+2, n+3, n+4, n+5}` of six consecutive integers. -/
def block (n : ℕ) : Finset ℕ := Finset.Icc n (n + 5)

/-- `A` is one part of a partition of `block n` into two parts with equal products. -/
def Balanced (n : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ block n ∧ ∏ x ∈ A, x = ∏ x ∈ block n \ A, x
