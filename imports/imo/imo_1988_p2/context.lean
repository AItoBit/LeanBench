namespace IMO1988P2

open Finset

section Config

variable {n : ℕ} {B : Type*} [DecidableEq B]

/-- The set of indices `i` such that `b ∈ A i`. -/
def idx (A : Fin (2 * n + 1) → Finset B) (b : B) : Finset (Fin (2 * n + 1)) :=
  Finset.univ.filter fun i => b ∈ A i

variable (A : Fin (2 * n + 1) → Finset B)
  (hcard : ∀ i, (A i).card = 2 * n)
  (hint : ∀ i j, i ≠ j → ((A i) ∩ (A j)).card = 1)
  (hmem : ∀ b : B, 2 ≤ (idx A b).card)

section InterElem

include hint

end InterElem

section Basic

variable {A}

variable {e : Fin (2 * n + 1) → Fin (2 * n + 1) → B}
  (he : ∀ i j, i ≠ j → A i ∩ A j = {e i j})

include he

include hmem in

include hcard hmem in

end Basic

include hcard hint hmem

end Config

section Distance

/-- The circular distance from `0` of an element of `Fin (2n+1)`. -/
def cls (n : ℕ) (x : Fin (2 * n + 1)) : ℕ := min x.val (2 * n + 1 - x.val)

end Distance

section Construction

variable {n : ℕ} {B : Type*} [DecidableEq B]

variable (A : Fin (2 * n + 1) → Finset B)
  (hcard : ∀ i, (A i).card = 2 * n)
  (hint : ∀ i j, i ≠ j → ((A i) ∩ (A j)).card = 1)
  (hmem : ∀ b : B, 2 ≤ (idx A b).card)

include hcard hint hmem

end Construction

section Existence

/-- The edges of the complete graph on `2n+1` vertices. -/
def Edge (n : ℕ) : Type := {p : Fin (2 * n + 1) × Fin (2 * n + 1) // p.1 < p.2}

instance (n : ℕ) : DecidableEq (Edge n) := Subtype.instDecidableEq

instance (n : ℕ) : Fintype (Edge n) := Subtype.fintype _

/-- The family of "stars": `star n i` is the set of edges incident to the vertex `i`. -/
def star (n : ℕ) (i : Fin (2 * n + 1)) : Finset (Edge n) :=
  Finset.univ.filter fun p => p.val.1 = i ∨ p.val.2 = i

/-- The edge joining two distinct vertices. -/
def edgeOf {n : ℕ} {i j : Fin (2 * n + 1)} (hij : i ≠ j) : Edge n :=
  ⟨(min i j, max i j), by
    rcases lt_or_gt_of_ne hij with h | h
    · rw [min_eq_left h.le, max_eq_right h.le]; exact h
    · rw [min_eq_right h.le, max_eq_left h.le]; exact h⟩

/-- `HasAssignment n` states that *every* family `A 0, …, A (2n)` of subsets of a set `B`
satisfying (a), (b), (c) admits an assignment of `0`/`1` to the elements of `B` for which each
`A i` has `0` assigned to exactly `n` of its elements. -/
def HasAssignment (n : ℕ) : Prop :=
  ∀ (B : Type) [DecidableEq B] (A : Fin (2 * n + 1) → Finset B),
    (∀ i, (A i).card = 2 * n) → (∀ i j, i ≠ j → ((A i) ∩ (A j)).card = 1) →
    (∀ b : B, 2 ≤ (idx A b).card) →
    ∃ f : B → Fin 2, ∀ i, ((A i).filter fun b => f b = 0).card = n
