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

/-- **IMO 1975, Problem 2.**

Let `a 1, a 2, a 3, …` be an infinite increasing sequence of positive integers.
Then for every `p ≥ 1` there are infinitely many `a m` which can be written in the form
`a m = x * a p + y * a q` with `x`, `y` positive integers and `q > p`.

The sequence is modelled as a function `a : ℕ → ℕ` which is strictly increasing and takes
positive values.  The conclusion says that the set of indices `m` for which such a
representation exists is infinite (equivalently, since `a` is injective, that infinitely
many terms `a m` are of that form).

The hypothesis `1 ≤ p` is part of the original statement (the sequence is indexed starting
from `1`); it is not needed for the proof. -/

theorem candidate (a : ℕ → ℕ) (hmono : StrictMono a) (hpos : ∀ n, 0 < a n)
    (p : ℕ) (hp : 1 ≤ p) :
    {m : ℕ | ∃ x y q : ℕ, 0 < x ∧ 0 < y ∧ p < q ∧ a m = x * a p + y * a q}.Infinite :=
