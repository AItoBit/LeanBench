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
# IMO 1969 Problem 6 and a generalization

The classical problem: for real numbers `x₁, x₂, y₁, y₂, z₁, z₂` with `x₁ > 0`, `x₂ > 0`,
`x₁ y₁ - z₁² > 0` and `x₂ y₂ - z₂² > 0`,
```
    8 / ((x₁ + x₂)(y₁ + y₂) - (z₁ + z₂)²) ≤ 1/(x₁y₁ - z₁²) + 1/(x₂y₂ - z₂²).
```

The generalization (with `n = m + 1`): for positive reals `a₁,…,a_n`, `b₁,…,b_n` with
`A = a₁⋯a_{n-1} - a_n^{n-1} > 0` and `B = b₁⋯b_{n-1} - b_n^{n-1} > 0`,
```
    2^n / (∏_{i<n} (aᵢ + bᵢ) - (a_n + b_n)^{n-1}) ≤ 1/A + 1/B.
```
Here the first `n - 1 = m` entries are indexed by `Finset.range m` and the last entry is
carried by the separate variables `an`, `bn`.

Remark on the proof.  The suggested intermediate step
`2^{n-2} (A + B) ≤ ∏_{i<n} (aᵢ + bᵢ) - (a_n + b_n)^{n-1}` is *false* in general (already for
`n = 3`: take `x₁ = y₁ = 1, z₁ = 0, x₂ = y₂ = 100, z₂ = 0`, where the left side is `20002`
and the right side is `10201`).  What is true, and what is proved below, is the weaker bound
`(A^{1/m} + B^{1/m})^m ≤ ∏_{i<n} (aᵢ + bᵢ) - (a_n + b_n)^{n-1}` (a consequence of the
superadditivity of the geometric mean together with Minkowski's inequality), which still
suffices since `2^{m+1} A B ≤ (A + B) (A^{1/m} + B^{1/m})^m`.
-/

namespace IMO1969P6
