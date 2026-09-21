open Finset

namespace Imo1992P3

set_option maxRecDepth 100000

/-- The 36 edges of `K₉`, as ordered pairs `i < j`. -/
def E : Finset (Fin 9 × Fin 9) := Finset.univ.filter (fun p => p.1 < p.2)

/-- The coloured edges of a colouring. -/
def colored (c : Fin 9 → Fin 9 → Option Bool) : Finset (Fin 9 × Fin 9) :=
  E.filter (fun p => c p.1 p.2 ≠ none)

/-- There is a triangle all of whose edges carry the same colour. -/
def HasMono (c : Fin 9 → Fin 9 → Option Bool) : Prop :=
  ∃ x y z : Fin 9, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ ∃ b : Bool,
    c x y = some b ∧ c y z = some b ∧ c x z = some b

instance (c : Fin 9 → Fin 9 → Option Bool) : Decidable (HasMono c) := by
  unfold HasMono
  infer_instance

/-! ### `R(3,3) ≤ 6` -/

/-- Two squares `0123` (red sides) and `4567` (blue sides) with all diagonals uncoloured,
plus `8` joined to the first square in blue and to the second in red, and `RᵢBⱼ` red exactly
when the indices have the same parity. -/
def ex : Fin 9 → Fin 9 → Option Bool := fun i j =>
  if (i : ℕ) = (j : ℕ) then none
  else if (i : ℕ) = 8 then (if (j : ℕ) < 4 then some false else some true)
  else if (j : ℕ) = 8 then (if (i : ℕ) < 4 then some false else some true)
  else if (i : ℕ) < 4 ∧ (j : ℕ) < 4 then
    (if ((i : ℕ) + (j : ℕ)) % 2 = 1 then some true else none)
  else if 4 ≤ (i : ℕ) ∧ 4 ≤ (j : ℕ) then
    (if ((i : ℕ) + (j : ℕ)) % 2 = 1 then some false else none)
  else some (decide (((i : ℕ) + (j : ℕ)) % 2 = 0))
