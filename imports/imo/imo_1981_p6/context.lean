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

namespace IMO1981P6

/-- The power tower of twos: `tower 0 = 1`, `tower (n+1) = 2 ^ tower n`.
So `tower n = 2^2^⋯^2` with `n` twos. -/
def tower : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 ^ tower n

section

variable (f : ℕ → ℕ → ℕ)
  (h1 : ∀ y, f 0 y = y + 1)
  (h2 : ∀ x, f (x + 1) 0 = f x 1)
  (h3 : ∀ x y, f (x + 1) (y + 1) = f x (f (x + 1) y))

include h1 h2 h3
