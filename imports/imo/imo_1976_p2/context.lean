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
# IMO 1976 Problem 2

Let `P₁(x) = x² - 2` and `P_j(x) = P₁(P_{j-1}(x))` for `j = 2, 3, …`.  We show that for any
positive integer `n` the roots of the equation `P_n(x) = x` are real and distinct: the real
polynomial `P_n - X` has degree `2 ^ n`, its multiset of real roots has exactly `2 ^ n`
elements (hence all of its complex roots are real), and these roots are pairwise distinct.

The proof follows the substitution `x = 2 cos θ`, under which `P_n(x) = 2 cos (2ⁿ θ)`.  The
`2 ^ n` numbers `2 cos (2π m / (4ⁿ - 1))`, where `m` runs over the multiples `k (2ⁿ + 1)`
(`0 ≤ k < 2ⁿ⁻¹`) and `i (2ⁿ - 1)` (`1 ≤ i ≤ 2ⁿ⁻¹`), are distinct solutions; since the degree is
`2 ^ n` there are no others and all are simple.
-/

namespace IMO1976P2

open Real Polynomial

/-- `P n` is the `n`-fold iterate of `x ↦ x² - 2`; in particular `P 1 = X ^ 2 - 2`. -/
noncomputable def P : ℕ → Polynomial ℝ
  | 0 => Polynomial.X
  | (n + 1) => (P n) ^ 2 - Polynomial.C 2

/-- The index of the `k`-th root, as a multiple of `2π / (4ⁿ - 1)`. -/
def rootIdx (n k : ℕ) : ℕ :=
  if k < 2 ^ (n - 1) then k * (2 ^ n + 1) else (k - 2 ^ (n - 1) + 1) * (2 ^ n - 1)

/-- The `k`-th root of `P n (x) = x`, for `k < 2ⁿ`. -/
noncomputable def rootVal (n k : ℕ) : ℝ :=
  2 * Real.cos (2 * π * (rootIdx n k) / (4 ^ n - 1))
