open Finset

open scoped Classical

noncomputable section

/-- The Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The number of points of `S` joined to `P` by a segment of length `d`
(the "diagonal degree" of `P`). -/
def deg (S : Finset Plane) (d : ℝ) (P : Plane) : ℕ :=
  (S.filter fun y => dist P y = d).card

/-- Ordered pairs of points of `S` at distance exactly `d`.
Each diagonal contributes `2`. -/
def pairCount (S : Finset Plane) (d : ℝ) : ℕ :=
  ((S ×ˢ S).filter fun p => dist p.1 p.2 = d).card

/-! ## Handshake -/

/-- The "middle point" property extracted from the plane geometry. -/
def MiddlePoint (d : ℝ) : Prop :=
  ∀ S : Finset Plane, (∀ x ∈ S, ∀ y ∈ S, dist x y ≤ d) →
    ∀ P ∈ S, 3 ≤ deg S d P → ∃ Q ∈ S, dist P Q = d ∧ deg S d Q = 1

/-! ## Main theorem -/
