open Finset

open scoped Nat

namespace Imo1987P1

/-- Number of fixed points of a permutation of `Fin n`. -/
def numFixed {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (univ.filter fun i => σ i = i).card

/-- `p n k` : number of permutations of `Fin n` with exactly `k` fixed points. -/
def p (n k : ℕ) : ℕ :=
  (univ.filter fun σ : Equiv.Perm (Fin n) => numFixed σ = k).card
