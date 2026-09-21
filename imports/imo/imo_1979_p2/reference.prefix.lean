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

namespace Imo1979P2

/-!
# IMO 1979, Problem 2

We consider a prism whose upper and lower bases are the pentagons `A₁A₂A₃A₄A₅` and
`B₁B₂B₃B₄B₅`.  Each of the ten sides of the two pentagons and each of the twenty-five
segments `AᵢBⱼ` is coloured red or blue.  Assume that in every triangle all of whose
sides are coloured, there is a red side and a blue side.  Then all ten sides of the two
pentagons have the same colour.

Formalisation.  Colours are modelled by `Bool`.

* `a i` is the colour of the pentagon side `Aᵢ Aᵢ₊₁`,
* `b j` is the colour of the pentagon side `Bⱼ Bⱼ₊₁`,
* `c i j` is the colour of the segment `Aᵢ Bⱼ`,

with indices in `Fin 5`, so that `i + 1` is the cyclic successor.  The triangles all of
whose sides are coloured are exactly the triangles `Aᵢ Aᵢ₊₁ Bⱼ` (with sides `a i`,
`c i j`, `c (i+1) j`) and `Aᵢ Bⱼ Bⱼ₊₁` (with sides `b j`, `c i j`, `c i (j+1)`); the
hypothesis says that these are not monochromatic.
-/

/-- On a 5-cycle, any two-colouring of the vertices has two adjacent vertices of the
same colour (the 5-cycle is not bipartite). -/
lemma exists_adj_eq (q : Fin 5 → Bool) : ∃ j : Fin 5, q j = q (j + 1) := by
  revert q; decide

/-- A set of vertices of a 5-cycle containing no two adjacent vertices has at most two
elements. -/
lemma indep_le_two (p : Fin 5 → Bool) (h : ∀ i : Fin 5, ¬ (p i = true ∧ p (i + 1) = true)) :
    (∑ i : Fin 5, if p i then 1 else 0) ≤ 2 := by
  revert p; decide

variable {a b : Fin 5 → Bool} {c : Fin 5 → Fin 5 → Bool}

/-- Neighbouring sides of the pentagon `A₁A₂A₃A₄A₅` have the same colour. -/
lemma a_succ_eq
    (hA : ∀ i j : Fin 5, ¬ (a i = c i j ∧ a i = c (i + 1) j))
    (hB : ∀ i j : Fin 5, ¬ (b j = c i j ∧ b j = c i (j + 1)))
    (i : Fin 5) : a (i + 1) = a i := by
  by_contra hne
  -- two cyclically adjacent `j`s with the segments `Aᵢ₊₁ Bⱼ`, `Aᵢ₊₁ Bⱼ₊₁` of equal colour `X`
  obtain ⟨j, hj⟩ := exists_adj_eq (fun j => c (i + 1) j)
  -- the triangle `Aᵢ₊₁ Bⱼ Bⱼ₊₁` forces `b j ≠ X`
  have e1 := hB (i + 1) j
  -- the triangles `Aᵢ Aᵢ₊₁ Bⱼ` and `Aᵢ Aᵢ₊₁ Bⱼ₊₁`
  have e2 := hA i j
  have e3 := hA i (j + 1)
  -- the triangle `Aᵢ Bⱼ Bⱼ₊₁`
  have e4 := hB i j
  -- the triangles `Aᵢ₊₁ Aᵢ₊₂ Bⱼ` and `Aᵢ₊₁ Aᵢ₊₂ Bⱼ₊₁`
  have e5 := hA (i + 1) j
  have e6 := hA (i + 1) (j + 1)
  -- the triangle `Aᵢ₊₂ Bⱼ Bⱼ₊₁`
  have e7 := hB (i + 1 + 1) j
  clear hA hB
  cases h1 : a i <;> cases h2 : a (i + 1) <;> cases h3 : b j <;>
    cases h4 : c i j <;> cases h5 : c i (j + 1) <;> cases h6 : c (i + 1) j <;>
    cases h7 : c (i + 1) (j + 1) <;> cases h8 : c (i + 1 + 1) j <;>
    cases h9 : c (i + 1 + 1) (j + 1) <;> simp_all

/-- All five sides of the pentagon `A₁A₂A₃A₄A₅` have the same colour. -/
lemma a_const
    (hA : ∀ i j : Fin 5, ¬ (a i = c i j ∧ a i = c (i + 1) j))
    (hB : ∀ i j : Fin 5, ¬ (b j = c i j ∧ b j = c i (j + 1)))
    (i : Fin 5) : a i = a 0 := by
  have h := a_succ_eq hA hB
  have h0 : a 1 = a 0 := by simpa using h 0
  have h1 : a 2 = a 1 := by simpa using h 1
  have h2 : a 3 = a 2 := by simpa using h 2
  have h3 : a 4 = a 3 := by simpa using h 3
  fin_cases i <;> simp_all

/-- All five sides of the pentagon `B₁B₂B₃B₄B₅` have the same colour. -/
lemma b_const
    (hA : ∀ i j : Fin 5, ¬ (a i = c i j ∧ a i = c (i + 1) j))
    (hB : ∀ i j : Fin 5, ¬ (b j = c i j ∧ b j = c i (j + 1)))
    (j : Fin 5) : b j = b 0 :=
  a_const (a := b) (b := a) (c := fun j i => c i j) (fun i j => hB j i) (fun i j => hA j i) j
