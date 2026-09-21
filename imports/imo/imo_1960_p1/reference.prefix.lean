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

set_option maxRecDepth 40000 in
/-- Bounded verification: for every `n < 1000`, the three-digit / divisibility /
digit-square condition holds exactly for `n = 550` and `n = 803`. -/
lemma imo_1960_p1_bounded :
    ∀ n ∈ Finset.range 1000,
      (((Nat.digits 10 n).length = 3 ∧ 11 ∣ n ∧
        ((Nat.digits 10 n).map (· ^ 2)).sum = (n / 11 : ℕ)) ↔ (n = 550 ∨ n = 803)) := by
  decide
