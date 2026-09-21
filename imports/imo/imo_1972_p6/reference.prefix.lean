open scoped BigOperators

open scoped Real

open scoped Nat

open scoped Classical

open scoped Pointwise

open scoped InnerProductSpace

set_option maxHeartbeats 8000000

set_option maxRecDepth 4000

set_option synthInstance.maxHeartbeats 20000

set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false

set_option autoImplicit false

set_option grind.warning false

/-!
# IMO 1972 Problem 6

*Given four distinct parallel planes, prove that there exists a regular tetrahedron with a
vertex on each plane.*

We model three-dimensional Euclidean space by `EuclideanSpace ℝ (Fin 3)`.  A family of four
parallel planes with common (nonzero) normal vector `n` is the family `{x | ⟪x, n⟫ = c i}`
for `i : Fin 4`; the planes are pairwise distinct exactly when `c` is injective.  A *regular
tetrahedron* is a family of four points whose pairwise distances are all equal to one and the
same positive number.

The construction: start from the reference regular tetrahedron `T` whose vertices are four
alternating vertices of a cube.  Its orthogonal projections onto a direction `w` are the four
numbers `⟪T i, w⟫`, and by solving a small linear system one can choose `w` so that these are
any four prescribed numbers of sum zero.  Rotating `w / ‖w‖` onto the unit normal `n / ‖n‖`
and scaling by `‖w‖` then places the four vertices on the four given planes.
-/

namespace IMO1972P6

/-- Three-dimensional Euclidean space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- Any unit vector of `E3` is the first vector of some orthonormal basis. -/
lemma exists_orthonormalBasis_first (w : E3) (hw : ‖w‖ = 1) :
    ∃ b : OrthonormalBasis (Fin 3) ℝ E3, b 0 = w := by
  have hcard : Module.finrank ℝ E3 = Fintype.card (Fin 3) := by simp
  have horth : Orthonormal ℝ (({0} : Set (Fin 3)).domRestrict (fun _ => w)) := by
    constructor
    · intro i; exact hw
    · intro i j hij
      exact absurd (Subtype.ext (by rw [i.2, j.2])) hij
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard horth
  exact ⟨b, hb 0 rfl⟩

/-- Any unit vector of `E3` can be mapped to any other unit vector by a linear isometry. -/
lemma exists_linearIsometryEquiv_map (u v : E3) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ∃ R : E3 ≃ₗᵢ[ℝ] E3, R v = u := by
  obtain ⟨b1, hb1⟩ := exists_orthonormalBasis_first v hv
  obtain ⟨b2, hb2⟩ := exists_orthonormalBasis_first u hu
  refine ⟨b1.repr.trans b2.repr.symm, ?_⟩
  simp [← hb1, ← hb2]

/-- The vertices of a reference regular tetrahedron: four alternating vertices of a cube. -/
def T : Fin 4 → E3 := ![!₂[1, 1, 1], !₂[1, -1, -1], !₂[-1, 1, -1], !₂[-1, -1, 1]]

/-- All six edges of the reference tetrahedron have length `2√2`. -/
lemma norm_T_sub (i j : Fin 4) (hij : i ≠ j) : ‖T i - T j‖ = 2 * Real.sqrt 2 := by
  have h : ∀ x : E3, (x.ofLp 0) ^ 2 + (x.ofLp 1) ^ 2 + (x.ofLp 2) ^ 2 = 8 →
      ‖x‖ = 2 * Real.sqrt 2 := by
    intro x hx
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
    simp only [Real.norm_eq_abs, sq_abs]
    rw [hx, show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num)]
  refine h _ ?_
  fin_cases i <;> fin_cases j <;> simp_all [T] <;> norm_num

/-- Given four reals `d 0, …, d 3` of sum zero, the explicit vector
`w = ((d 0 + d 1)/2, (d 0 + d 2)/2, (d 0 + d 3)/2)` has `⟪T i, w⟫ = d i` for every `i`:
the reference tetrahedron projects onto the direction `w` exactly at the prescribed levels. -/
lemma inner_T_w (d : Fin 4 → ℝ) (hd : d 0 + d 1 + d 2 + d 3 = 0) (i : Fin 4) :
    ⟪T i, (!₂[(d 0 + d 1) / 2, (d 0 + d 2) / 2, (d 0 + d 3) / 2] : E3)⟫_ℝ = d i := by
  fin_cases i <;>
    · simp [T, PiLp.inner_apply, Fin.sum_univ_three]
      linarith [hd]
