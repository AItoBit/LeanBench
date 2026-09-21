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
# IMO 1974, Problem 1

Three players `A`, `B`, `C` play the following game.  On each of three cards an integer is
written; these three numbers `p, q, r` satisfy `0 < p < q < r`.  The three cards are shuffled
and one is dealt to each player; each player then receives the number of counters indicated by
the card he holds.  Then the cards are shuffled again, and this is repeated for `n ≥ 2` rounds.

After the last round `A` has `20` counters in all, `B` has `10` and `C` has `9`.  In the last
round `B` received `r` counters.  Who received `q` counters in the first round?

Answer: player `C`.

Formalisation.  Rounds are indexed by `i < n`.  `a i`, `b i`, `c i` denote the numbers of
counters received by `A`, `B`, `C` in round `i`; the fact that in each round the three cards
`p, q, r` are distributed among the three players is expressed by the equality of multisets
`{a i, b i, c i} = {p, q, r}`.
-/

namespace IMO1974P1
