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

namespace IMO2001P6

/-- Rearrangement of the hypothesis `K*M + L*N = (K+L-M+N)*(-K+L+M+N)`. -/
theorem sq_rearrange {K L M N : ℤ}
    (heq : K * M + L * N = (K + L - M + N) * (-K + L + M + N)) :
    K ^ 2 - K * M + M ^ 2 = L ^ 2 + L * N + N ^ 2 := by
  linear_combination heq

/-- The key factorization identity:
`(K*M + L*N) * (L^2 + L*N + N^2) = (K*L + M*N) * (K*N + L*M)`. -/
theorem key_identity {K L M N : ℤ}
    (heq : K * M + L * N = (K + L - M + N) * (-K + L + M + N)) :
    (K * M + L * N) * (L ^ 2 + L * N + N ^ 2) = (K * L + M * N) * (K * N + L * M) := by
  linear_combination (-(L * N)) * sq_rearrange heq
