open scoped BigOperators

open scoped Real

open scoped Nat

open scoped Classical

open scoped Pointwise

set_option maxHeartbeats 8000000

set_option maxRecDepth 4000

set_option relaxedAutoImplicit false

set_option autoImplicit false

set_option grind.warning false

/-!
# IMO 2007, Problem 6 (Upper Bound)

Let `n` be a positive integer. Consider
`S = {(x, y, z) : x, y, z ∈ {0, 1, …, n}, x + y + z > 0}`
as a set of `(n+1)^3 - 1` points in three dimensional space. 

This formalization proves the constructive upper bound: 
The set `S` can be covered by exactly `3 * n` planes without covering the origin `(0,0,0)`.
-/

namespace IMO2007P6

/-- The set `S` of the problem: the lattice points of the cube `{0,…,n}^3`, origin removed. -/
def gridS (n : ℕ) : Set (ℝ × ℝ × ℝ) :=
  {p | ∃ x y z : ℕ, x ≤ n ∧ y ≤ n ∧ z ≤ n ∧ 0 < x + y + z ∧
      p = ((x : ℝ), (y : ℝ), (z : ℝ))}

/-- The plane `a * X + b * Y + c * Z = d` of `ℝ³`. -/
def planeSet (a b c d : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | a * p.1 + b * p.2.1 + c * p.2.2 = d}

theorem mem_planeSet {a b c d : ℝ} {p : ℝ × ℝ × ℝ} :
    p ∈ planeSet a b c d ↔ a * p.1 + b * p.2.1 + c * p.2.2 = d := Iff.rfl

/-- `CoversS n m` says that there are `m` planes of `ℝ³` whose union contains the set
`gridS n` but does not contain the origin. -/
def CoversS (n m : ℕ) : Prop :=
  ∃ A B C D : Fin m → ℝ,
    (∀ j, ¬ (A j = 0 ∧ B j = 0 ∧ C j = 0)) ∧
    gridS n ⊆ (⋃ j, planeSet (A j) (B j) (C j) (D j)) ∧
    ((0 : ℝ), (0 : ℝ), (0 : ℝ)) ∉ (⋃ j, planeSet (A j) (B j) (C j) (D j))

/-! ### The upper bound: `3 * n` planes suffice -/
