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

/-!
# IMO 2007, Problem 3

In a mathematical competition some competitors are friends. Friendship is always mutual.
Call a group of competitors a *clique* if each two of them are friends.  (In particular,
any group of fewer than two competitors is a clique.)  The number of members of a clique
is called its *size*.

Given that, in this competition, the largest size of a clique is *even*, prove that the
competitors can be arranged into two rooms such that the largest size of a clique
contained in one room is the same as the largest size of a clique contained in the other
room.

Competitors are modelled by a finite type `V`, friendship by a `SimpleGraph V`, and a room
by a `Finset V` (the other room being its complement).  The quantity
`cliqueSize G T` is the largest size of a clique all of whose members belong to the
room `T`.

## Outline of the proof

Let `M` be a clique of maximum size `2 * m`.  Among all subsets `S ⊆ M`, pick one of least
size with `cliqueSize G Sᶜ ≤ S.card` (the room `S` is a clique, so its largest clique size
is `S.card`).  If equality holds we are done.  Otherwise, deleting one competitor from `S`
gives a room `M₁` with `cliqueSize G M₁ = M₁.card = m₁` and `cliqueSize G M₁ᶜ = m₁ + 1`;
this is handled by the lemma `repair`.  Write `M₂ = M \ M₁`; since `M₂` is a clique in the
second room, `M₂.card ≤ m₁ + 1`, and because the maximum clique size `2 * m` is *even* this
forces `m ≤ m₁`, i.e. the number `r = 2 * m₁ + 1 - 2 * m` is at least `1`.  (For an odd
maximum clique size the corresponding number can vanish, and indeed a triangle is a
counterexample to the statement without the evenness hypothesis.)  Two cases:

* some member `u` of `M₂` is missing from some largest clique `C` of the second room: then
  moving `u` into the first room gives two rooms with largest clique size `m₁ + 1`;
* otherwise every largest clique of the second room contains `M₂`.  Consider the set
  `Bstar` of competitors outside `M` who are friends of everybody in `M₂`; its cliques
  have size at most `r`, and size `r` is attained.  Choose an inclusion-minimal set
  `U ⊆ Bstar` meeting every clique of size `r` in `Bstar`, and move `U` into the first
  room.  Both rooms then have largest clique size exactly `m₁`.
-/

namespace IMO2007P3

open Finset

variable {V : Type*} [DecidableEq V]

/-- `cliqueSize G T` is the largest size of a clique of `G` all of whose members lie in
the room `T`. -/
noncomputable def cliqueSize (G : SimpleGraph V) (T : Finset V) : ℕ :=
  (T.powerset.filter (fun s : Finset V => G.IsClique (s : Set V))).sup Finset.card

section Main

variable [Fintype V]
