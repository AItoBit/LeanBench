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
# IMO 1988, Problem 6

Let `a` and `b` be positive integers such that `a * b + 1` divides `a ^ 2 + b ^ 2`.
Show that `(a ^ 2 + b ^ 2) / (a * b + 1)` is the square of an integer.

The proof is the classical "Vieta jumping" descent argument.
-/

namespace Imo1988Q6
