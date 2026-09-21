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

namespace IMO1978Q6

/-- A colouring `c` of the numbers `1, …, 1978` by six countries is `SumFreeColoring`
if no member's number is the sum of the numbers of two members of his own country. -/
def SumFreeColoring (c : ℕ → Fin 6) : Prop :=
  ∀ x y : ℕ, 0 < x → 0 < y → x + y ≤ 1978 → c x = c (x + y) → c y = c (x + y) → False

/-- The invariant carried through the pigeonhole induction: `T` is a set of numbers in
`[1, 1978]`, none of whose elements, and none of whose positive pairwise differences,
receives a colour from the set `F` of already-discarded colours. -/
def Inv (c : ℕ → Fin 6) (T : Finset ℕ) (F : Finset (Fin 6)) : Prop :=
  (∀ t ∈ T, 0 < t ∧ t ≤ 1978) ∧ (∀ t ∈ T, c t ∉ F) ∧
    (∀ t ∈ T, ∀ t' ∈ T, t < t' → c (t' - t) ∉ F)
