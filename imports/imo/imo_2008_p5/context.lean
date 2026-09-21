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
# IMO 2008 Problem 5

Let `n` and `k` be positive integers with `k ≥ n` and `k - n` even.  There are `2 * n` lamps,
labelled `1, …, 2n`, all initially off.  A *sequence of steps* of length `k` is a list of `k`
lamps, the `i`-th entry being the lamp switched at step `i`.

* `N` is the number of such sequences ending in the state where lamps `1, …, n` are on and
  lamps `n+1, …, 2n` are off;
* `M` is the number of such sequences ending in the same state in which, moreover, none of the
  lamps `n+1, …, 2n` is ever switched.

The answer is `N / M = 2 ^ (k - n)`.

Since a lamp starts off, it is on at the end iff it has been switched an odd number of times;
so the final state condition says exactly that each of the first `n` lamps is switched an odd
number of times and each of the last `n` lamps an even number of times.  A lamp among
`n+1, …, 2n` is never switched on iff it is never switched at all.  This is how the two counts
are formalised below, sequences being modelled as functions `Fin k → Fin (2 * n)`.
-/

namespace Imo2008P5

/-- The number of steps at which the lamp `i` is switched, in the sequence of steps `a`. -/
def cnt {k : ℕ} {L : Type} [DecidableEq L] (a : Fin k → L) (i : L) : ℕ :=
  (Finset.univ.filter fun t => a t = i).card

/-- The set of sequences of `k` steps on `2 * n` lamps ending in the state where the lamps
`1, …, n` (indices `0, …, n-1`) are on and the lamps `n+1, …, 2n` (indices `n, …, 2n-1`)
are off.  `N` is the cardinality of this set. -/
def Nset (n k : ℕ) : Finset (Fin k → Fin (2 * n)) :=
  Finset.univ.filter fun a =>
    (∀ i : Fin (2 * n), (i : ℕ) < n → Odd (cnt a i)) ∧
      (∀ i : Fin (2 * n), n ≤ (i : ℕ) → Even (cnt a i))

/-- The subset of `Nset n k` consisting of those sequences in which none of the last `n` lamps
is ever switched.  `M` is the cardinality of this set. -/
def Mset (n k : ℕ) : Finset (Fin k → Fin (2 * n)) :=
  (Nset n k).filter fun a => ∀ t, (a t : ℕ) < n

/-! ### Reformulation with lamps indexed by `Fin n ⊕ Fin n` -/

/-- The identification of the `2 * n` lamps with two copies of `Fin n`: the first copy is the
set `A = {1, …, n}` of lamps that must end up on, the second copy is the set
`B = {n+1, …, 2n}`. -/
def lampEquiv (n : ℕ) : Fin (2 * n) ≃ Fin n ⊕ Fin n :=
  (finCongr (two_mul n)).trans finSumFinEquiv.symm

/-- `Nset` transported along `lampEquiv`. -/
def NsetS (n k : ℕ) : Finset (Fin k → Fin n ⊕ Fin n) :=
  Finset.univ.filter fun a =>
    (∀ i : Fin n, Odd (cnt a (Sum.inl i))) ∧ (∀ i : Fin n, Even (cnt a (Sum.inr i)))

/-- `Mset` transported along `lampEquiv`. -/
def MsetS (n k : ℕ) : Finset (Fin k → Fin n ⊕ Fin n) :=
  (NsetS n k).filter fun a => ∀ t, (a t).isLeft

/-- Sequences using only the lamps of `A`, each an odd number of times. -/
def Aset (n k : ℕ) : Finset (Fin k → Fin n) :=
  Finset.univ.filter fun y => ∀ i : Fin n, Odd (cnt y i)

/-- Forgetting which copy of `Fin n` a lamp belongs to. -/
def proj {n k : ℕ} (a : Fin k → Fin n ⊕ Fin n) : Fin k → Fin n := fun t => Sum.elim id id (a t)

/-! ### Basic lemmas on `cnt` -/

/-- The set of `ZMod 2`-valued functions that sum to zero on every fibre of `y`. -/
def Kset {n k : ℕ} (y : Fin k → Fin n) : Finset (Fin k → ZMod 2) :=
  Finset.univ.filter fun s => ∀ i : Fin n, ∑ t ∈ Finset.univ.filter fun t => y t = i, s t = 0

/-- Summing a `ZMod 2`-valued function over the fibres of `y`, as a linear map. -/
def fibreSum {n k : ℕ} (y : Fin k → Fin n) : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) where
  toFun s := fun i => ∑ t ∈ Finset.univ.filter fun t => y t = i, s t
  map_add' := by
    intro s s'
    funext i
    simp [Finset.sum_add_distrib]
  map_smul' := by
    intro c s
    funext i
    simp [Finset.mul_sum]
