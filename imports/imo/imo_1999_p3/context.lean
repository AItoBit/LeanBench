namespace Imo1999P3

open Finset

/-- The cells of the `n × n` board, as pairs `(row, column)` with entries `< n`. -/
def board (n : ℕ) : Finset (ℕ × ℕ) := Finset.range n ×ˢ Finset.range n

/-- Two cells are neighbouring when they have a common side. -/
def Adj (c d : ℕ × ℕ) : Prop :=
  (c.1 = d.1 ∧ (c.2 + 1 = d.2 ∨ d.2 + 1 = c.2)) ∨ (c.2 = d.2 ∧ (c.1 + 1 = d.1 ∨ d.1 + 1 = c.1))

instance (c d : ℕ × ℕ) : Decidable (Adj c d) := by unfold Adj; infer_instance

/-- A set of marked cells is *good* when every cell of the board has a marked neighbour. -/
def Good (n : ℕ) (S : Finset (ℕ × ℕ)) : Prop := ∀ c ∈ board n, ∃ s ∈ S, Adj c s

/-- The marked black cells: on the diagonals `i + j ≡ 0 [MOD 4]`, every other cell counted
from the border. -/
def Pset (n : ℕ) : Finset (ℕ × ℕ) :=
  (board n).filter fun c =>
    (c.1 + c.2) % 4 = 0 ∧ ((c.1 + c.2 < n ∧ c.1 % 2 = 0) ∨ (n ≤ c.1 + c.2 ∧ c.1 % 2 = 1))

/-- Reflection of the board in a vertical axis; it exchanges the two colours. -/
def refl (n : ℕ) (c : ℕ × ℕ) : ℕ × ℕ := (c.1, n - 1 - c.2)

/-- The marked cells. -/
def Qset (n : ℕ) : Finset (ℕ × ℕ) := Pset n ∪ (Pset n).image (refl n)

/-! ### The set `Pset` dominates the white cells exactly once -/
