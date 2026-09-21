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
# IMO 1994 Problem 3

For any positive integer `k`, let `f k` be the number of elements in the set
`{k+1, k+2, ..., 2k}` whose base 2 representation has precisely three `1`s.

(a) For each positive integer `m` there is at least one `k` with `f k = m`.
(b) The positive integers `m` for which there is exactly one such `k` are exactly
    the numbers `n(n-1)/2 + 1` with `n ≥ 2`.
-/

namespace IMO1994P3

/-- The number of `1`s in the base 2 representation of `n`. -/
def onesCount (n : ℕ) : ℕ := (Nat.digits 2 n).sum

/-- `f k` is the number of elements of `{k+1, …, 2k}` whose base 2 representation
has precisely three `1`s. -/
def f (k : ℕ) : ℕ :=
  ((Finset.Ico (k + 1) (2 * k + 1)).filter (fun x => onesCount x = 3)).card

/-! ### Basic facts about `onesCount` -/

private def gg (x : ℕ) : ℕ := if onesCount x = 3 then 1 else 0
