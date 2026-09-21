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

/-- The quadratic `y^2 + y - 1 = 0` holds exactly for the two values `(-1 ± √5)/2`. -/
theorem imo_1963_p4_quadratic_iff (y : ℝ) :
    y ^ 2 + y - 1 = 0 ↔ y = (-1 + √5) / 2 ∨ y = (-1 - √5) / 2 := by
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  constructor
  · intro h
    have hfac : (y - (-1 + √5) / 2) * (y - (-1 - √5) / 2) = 0 := by
      have hexp : (y - (-1 + √5) / 2) * (y - (-1 - √5) / 2)
          = y ^ 2 + y - 1 + (5 - √5 ^ 2) / 4 := by ring
      rw [hexp, h, h5]; ring
    rcases mul_eq_zero.mp hfac with h' | h'
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> nlinarith [h5]
