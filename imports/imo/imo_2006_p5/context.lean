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
# IMO 2006, Problem 5

Let `P(x)` be a polynomial of degree `n > 1` with integer coefficients and let `k` be a positive
integer. Consider the polynomial `Q(x) = P(P(...P(P(x))...))`, where `P` occurs `k` times.
Prove that there are at most `n` integers `t` such that `Q(t) = t`.

The formalization below states the problem for `P : ℤ[X]` with `1 < P.natDegree`, with `Q` given by
`Imo2006P5.iterComp P k = P.comp^[k] X`.  The final results are
`Imo2006P5.imo2006_p5` (any finite set of solutions has at most `n` elements),
`Imo2006P5.imo2006_p5_setOf_finite` and `Imo2006P5.imo2006_p5_ncard` (the set of solutions is
finite and has at most `n` elements).

The proof follows the solution on the AoPS wiki (the same route as the corresponding entry in
Mathlib's archive of IMO problems): the key step is that `P^[k] t = t` forces
`P (P t) = t`, which reduces the problem to `k = 2`; that case is handled by exhibiting a nonzero
polynomial of degree `n` vanishing at every solution.
-/

namespace Imo2006P5

open Function Polynomial

/-- The `k`-fold composite `Q(x) = P(P(...P(x)...))` of a polynomial `P` with itself. -/
noncomputable def iterComp (P : ℤ[X]) (k : ℕ) : ℤ[X] := P.comp^[k] X
