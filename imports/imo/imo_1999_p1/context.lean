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

/-!
# IMO 1999, Problem 1

Determine all finite sets `S` of at least three points in the plane which satisfy the following
condition: for any two distinct points `A` and `B` in `S`, the perpendicular bisector of the
segment `AB` is an axis of symmetry of `S`.

The answer: `S` is the set of vertices of a regular `n`-gon, where `n = |S|`.

The plane is modelled by `ℂ`.  The reflection in the perpendicular bisector of a segment `AB`
(with `A ≠ B`) is the map `reflBis A B`, defined below; the lemmas `reflBis_dist`,
`reflBis_involutive` and `reflBis_fixed_iff` justify this name: `reflBis A B` is an isometric
involution of the plane whose set of fixed points is exactly the perpendicular bisector
`{z | dist z A = dist z B}` of `A` and `B`.
-/

namespace IMO1999Q1

open ComplexConjugate

/-- Reflection of the plane `ℂ` in the perpendicular bisector of the segment joining `A` to `B`
(for `A ≠ B`). -/
noncomputable def reflBis (A B z : ℂ) : ℂ :=
  (A + B) / 2 - ((B - A) / conj (B - A)) * conj (z - (A + B) / 2)

section Basic

variable {A B z z' : ℂ}

instance perpBisector_nonempty_complex (A B : ℂ) :
    Nonempty (AffineSubspace.perpBisector A B) :=
  ⟨⟨midpoint ℝ A B, AffineSubspace.midpoint_mem_perpBisector A B⟩⟩

end Basic

section Forward

variable {S : Finset ℂ}

/-- The symmetry hypothesis of the problem. -/
def IsSymmetric (S : Finset ℂ) : Prop :=
  ∀ A ∈ S, ∀ B ∈ S, A ≠ B → ∀ z ∈ S, reflBis A B z ∈ S

end Forward
