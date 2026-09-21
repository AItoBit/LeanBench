open scoped BigOperators

open scoped Real

open scoped Nat

open scoped Pointwise

set_option maxHeartbeats 1000000

set_option maxRecDepth 4000

set_option relaxedAutoImplicit false

set_option autoImplicit false

/-!
# IMO 1990, Problem 2

Let `n ≥ 3` and consider a set `E` of `2n - 1` distinct points on a circle.  Suppose that exactly
`k` of these points are to be coloured black.  Such a colouring is *good* if there is at least one
pair of black points such that the interior of one of the arcs between them contains exactly `n`
points from `E`.  Find the smallest value of `k` such that every such colouring of `k` points of
`E` is good.

We label the `2n - 1` points of `E` by `ZMod (2 * n - 1)`, in cyclic order along the circle; the
number of points of `E` in the interior of the arc going (say) clockwise from `x` to `y` is then
`(y - x).val - 1`.

The answer is `n` when `3 ∤ 2n - 1` and `3 * ⌊(2n-1)/6⌋ + 1` when `3 ∣ 2n - 1`.
-/

namespace Imo1990P2

/-- `gcd3 n` is `gcd (2n-1) 3`; it is `3` if `3 ∣ 2n - 1` and `1` otherwise.  It is the number of
cycles into which the "arc containing exactly `n` points" relation splits the `2n-1` points. -/
def gcd3 (n : ℕ) : ℕ := Nat.gcd (2 * n - 1) 3

/-- The common length of these cycles. -/
def cyclen (n : ℕ) : ℕ := (2 * n - 1) / gcd3 n

/-- Two points of `E` are joined when they differ by this step. -/
def step (n : ℕ) : ZMod (2 * n - 1) := ((n + 1 : ℕ) : ZMod (2 * n - 1))

/-- A colouring, given by the set `S` of black points, is *good* if some pair of distinct black
points bounds an arc whose interior contains exactly `n` points of `E`. -/
def IsGood (n : ℕ) (S : Finset (ZMod (2 * n - 1))) : Prop :=
  ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ ((y - x).val - 1 = n ∨ (x - y).val - 1 = n)

/-- The answer to the problem. -/
def answer (n : ℕ) : ℕ := if 3 ∣ (2 * n - 1) then 3 * ((2 * n - 1) / 6) + 1 else n

/-! ### Elementary arithmetic facts -/

/-- A colouring which is not good and has the maximal possible number of black points: in each of
the `gcd3 n` cycles, take every other point. -/
def badSet (n : ℕ) : Finset (ZMod (2 * n - 1)) :=
  (Finset.range (gcd3 n) ×ˢ Finset.range ((cyclen n - 1) / 2)).image
    (fun p => ((p.1 + 3 * p.2 : ℕ) : ZMod (2 * n - 1)))
