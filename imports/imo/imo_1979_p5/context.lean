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
# IMO 1979 Problem 5

Determine all real numbers `a` for which there exist non-negative reals
`x₁, …, x₅` satisfying

`∑ k x_k = a`,  `∑ k³ x_k = a²`,  `∑ k⁵ x_k = a³`.

The answer is `a ∈ {0, 1, 4, 9, 16, 25}`.
-/

namespace Imo1979P5

/-- The three defining relations for a candidate value `a`, with the non-negative
reals `x₁, …, x₅` given as the values at `1, …, 5` of a function `x : ℕ → ℝ`. -/
def Sols (a : ℝ) : Prop :=
  ∃ x : ℕ → ℝ, (∀ k ∈ Finset.Icc 1 5, 0 ≤ x k) ∧
    (∑ k ∈ Finset.Icc (1 : ℕ) 5, (k : ℝ) * x k = a) ∧
    (∑ k ∈ Finset.Icc (1 : ℕ) 5, (k : ℝ) ^ 3 * x k = a ^ 2) ∧
    (∑ k ∈ Finset.Icc (1 : ℕ) 5, (k : ℝ) ^ 5 * x k = a ^ 3)

end Imo1979P5
