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
# IMO 1979, Problem 1

If `p` and `q` are natural numbers so that

`p / q = 1 - 1/2 + 1/3 - 1/4 + ... - 1/1318 + 1/1319`,

prove that `p` is divisible by `1979`.
-/

namespace IMO1979Q1

/-- The index set `{660, 661, ..., 1319}`. -/
def I : Finset ℕ := Finset.Icc 660 1319

/-- The product of all elements of `I`. -/
def D : ℤ := ∏ k ∈ I, (k : ℤ)

/-- `A = ∑_{k ∈ I} ∏_{m ∈ I, m ≠ k} m`, i.e. the numerator of `∑_{k ∈ I} 1/k`
over the common denominator `D`. -/
def A : ℤ := ∑ k ∈ I, ∏ m ∈ I.erase k, (m : ℤ)
