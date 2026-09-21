open scoped BigOperators

open scoped Classical

set_option maxHeartbeats 1000000

/-!
# IMO 2009, Problem 6 (the grasshopper problem)

Let `a₁, a₂, …, aₙ` be distinct positive integers and let `M` be a set of `n - 1` positive
integers not containing `s = a₁ + a₂ + ⋯ + aₙ`.  A grasshopper is to jump along the real axis,
starting at the point `0` and making `n` jumps to the right with lengths `a₁, a₂, …, aₙ` in some
order.  Prove that the order can be chosen in such a way that the grasshopper never lands on any
point in `M`.

The jump lengths are modelled by a list `l : List ℕ` of distinct positive integers, and choosing
an order means choosing a permutation `l'` of `l`.  The points the grasshopper visits are the
partial sums `(l'.take k).sum` for `k ≥ 1`.
-/

namespace IMO2009P6

open List

/-- `SafeFrom M p l` says that a grasshopper standing at the point `p` and performing the jumps
of `l` in order never lands on a point of `M`; if `l` is empty this asserts that `p` itself is
not in `M`. -/
def SafeFrom (M : Finset ℕ) : ℕ → List ℕ → Prop
  | p, [] => p ∉ M
  | p, a :: t => p + a ∉ M ∧ SafeFrom M (p + a) t
