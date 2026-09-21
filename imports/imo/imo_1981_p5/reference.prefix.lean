open scoped BigOperators

open scoped Real

open scoped Nat

open scoped Classical

open scoped Pointwise

open RealInnerProductSpace

set_option maxHeartbeats 8000000

set_option maxRecDepth 4000

set_option synthInstance.maxHeartbeats 20000

set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false

set_option autoImplicit false

/-!
# IMO 1981, Problem 5

*Three congruent circles have a common point `O` and lie inside a given triangle.  Each circle
touches a pair of sides of the triangle.  Prove that the incenter and the circumcenter of the
triangle and the point `O` are collinear.*

The configuration is formalised in the Euclidean plane `EuclideanSpace ℝ (Fin 2)`:

* the triangle is given by three non-collinear points `A`, `B`, `C`;
* the three circles have a common radius `r` and centres `OA`, `OB`, `OC`, each of which lies
  inside the triangle (i.e. in the convex hull of `{A, B, C}`);
* the circle with centre `OA` is tangent to the lines `AB` and `AC`, the circle with centre `OB`
  is tangent to `AB` and `BC`, and the circle with centre `OC` is tangent to `AC` and `BC`;
* `O` lies on all three circles;
* `X` is a circumcenter of the triangle, i.e. a point equidistant from `A`, `B` and `C`.

One nondegeneracy assumption has to be added: the three circles must not all coincide.  (If the
common radius equals the inradius, then all three circles are the incircle, every point `O` of
the incircle satisfies the hypotheses, and the conclusion fails.)  We express this as
`OA ≠ OB`.

The conclusion is that the incenter, the circumcenter `X` and `O` are collinear.
-/

namespace IMO1981P5

/-- Points of the Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-! ### Elementary inner-product computations -/

theorem norm_lin_comb_sq (a b : ℝ) (u v : Pt) :
    ‖a • u + b • v‖ ^ 2 = a ^ 2 * ‖u‖ ^ 2 + 2 * a * b * ⟪u, v⟫ + b ^ 2 * ‖v‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_comm v u, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem inner_lin_comb (a b : ℝ) (u v : Pt) :
    ⟪a • u + b • v, u⟫ = a * ‖u‖ ^ 2 + b * ⟪u, v⟫ := by
  simp only [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
    real_inner_comm v u]

theorem inner_coord (x y : Pt) : ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]; ring

theorem normsq_coord (x : Pt) : ‖x‖ ^ 2 = x 0 * x 0 + x 1 * x 1 := by
  rw [← real_inner_self_eq_norm_sq, inner_coord]

/-- In the plane, a vector orthogonal to two linearly independent vectors vanishes. -/
theorem eq_zero_of_orthogonal_two (w u v : Pt) (h1 : ⟪w, u⟫ = 0) (h2 : ⟪w, v⟫ = 0)
    (hd : 0 < ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2) : w = 0 := by
  rw [inner_coord] at h1 h2
  rw [normsq_coord, normsq_coord, inner_coord] at hd
  have hdet : u 0 * v 1 - u 1 * v 0 ≠ 0 := by
    intro h
    rw [show (u 0 * u 0 + u 1 * u 1) * (v 0 * v 0 + v 1 * v 1) - (u 0 * v 0 + u 1 * v 1) ^ 2
      = (u 0 * v 1 - u 1 * v 0) ^ 2 by ring, h] at hd
    simp at hd
  have e0 : w 0 * (u 0 * v 1 - u 1 * v 0) = 0 := by linear_combination v 1 * h1 - u 1 * h2
  have e1 : w 1 * (u 0 * v 1 - u 1 * v 0) = 0 := by linear_combination u 0 * h2 - v 0 * h1
  have f0 := (mul_eq_zero.1 e0).resolve_right hdet
  have f1 := (mul_eq_zero.1 e1).resolve_right hdet
  ext i; fin_cases i <;> simpa

/-- Two points that are both equidistant from `P` and from `Q` differ by a vector orthogonal
to `Q - P`. -/
theorem inner_eq_zero_of_dist_eq (P Q Z W : Pt) (h1 : dist Z P = dist Z Q)
    (h2 : dist W P = dist W Q) : ⟪Z - W, Q - P⟫ = 0 := by
  have e : ∀ Y : Pt, dist Y P = dist Y Q → 2 * ⟪Y, Q⟫ - 2 * ⟪Y, P⟫ = ‖Q‖ ^ 2 - ‖P‖ ^ 2 := by
    intro Y hY
    have : ‖Y - P‖ ^ 2 = ‖Y - Q‖ ^ 2 := by rw [← dist_eq_norm, ← dist_eq_norm, hY]
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq] at this
    simp only [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq] at this
    rw [real_inner_comm Y P, real_inner_comm Y Q] at this
    linarith
  have hZ := e Z h1
  have hW := e W h2
  simp only [inner_sub_left, inner_sub_right]
  linarith

/-! ### The Gram determinant of a triangle -/

/-- Twice the area of the triangle `A B C`, squared:
`gram A B C = ‖B - A‖² ‖C - A‖² - ⟪B - A, C - A⟫²`. -/
noncomputable def gram (A B C : Pt) : ℝ :=
  ‖B - A‖ ^ 2 * ‖C - A‖ ^ 2 - ⟪B - A, C - A⟫ ^ 2

theorem gram_nonneg (A B C : Pt) : 0 ≤ gram A B C := by
  have h1 := abs_real_inner_le_norm (B - A) (C - A)
  have h2 := sq_abs (⟪B - A, C - A⟫)
  simp only [gram]
  nlinarith [abs_nonneg (⟪B - A, C - A⟫), norm_nonneg (B - A), norm_nonneg (C - A)]

theorem gram_swap (A B C : Pt) : gram A C B = gram A B C := by
  simp only [gram, real_inner_comm (C - A) (B - A)]; ring

theorem gram_cycl (A B C : Pt) : gram B C A = gram A B C := by
  simp only [gram, ← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, real_inner_comm]
  ring

theorem collinear_of_gram_eq_zero (A B C : Pt) (h : gram A B C = 0) :
    Collinear ℝ ({A, B, C} : Set Pt) := by
  set u := B - A with hu
  set v := C - A with hv
  by_cases hu0 : u = 0
  · have hB : B = A := by rw [← sub_eq_zero]; exact hu0
    subst hB
    exact (collinear_pair ℝ B C).subset (by intro x hx; simp at hx ⊢; tauto)
  · have hnu : ‖u‖ ≠ 0 := by simpa using hu0
    have key : ‖(‖u‖ ^ 2) • v + (-⟪u, v⟫) • u‖ ^ 2 = 0 := by
      rw [norm_lin_comb_sq, real_inner_comm u v]
      simp only [gram, ← hu, ← hv] at h
      nlinarith [h]
    have key2 : (‖u‖ ^ 2) • v = ⟪u, v⟫ • u := by
      have h0 : ‖(‖u‖ ^ 2) • v + (-⟪u, v⟫) • u‖ = 0 := by
        nlinarith [norm_nonneg ((‖u‖ ^ 2) • v + (-⟪u, v⟫) • u)]
      have h3 : (‖u‖ ^ 2) • v - ⟪u, v⟫ • u = 0 := by
        rw [← norm_eq_zero.1 h0]; module
      exact sub_eq_zero.1 h3
    have hvk : v = (⟪u, v⟫ / ‖u‖ ^ 2) • u := by
      have hne : (‖u‖ ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 hnu
      rw [div_eq_inv_mul, mul_smul, ← key2, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [collinear_iff_of_mem (Set.mem_insert A {B, C})]
    refine ⟨u, ?_⟩
    rintro p (rfl | rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp [hu]⟩
    · exact ⟨⟪u, v⟫ / ‖u‖ ^ 2, by rw [← hvk, hv]; simp⟩

theorem gram_pos (A B C : Pt) (h : ¬ Collinear ℝ ({A, B, C} : Set Pt)) : 0 < gram A B C := by
  rcases (gram_nonneg A B C).lt_or_eq with h' | h'
  · exact h'
  · exact absurd (collinear_of_gram_eq_zero A B C h'.symm) h

/-! ### Tangency -/

/-- The circle with centre `P` and radius `r` is tangent to the line `AB`: the foot of the
perpendicular dropped from `P` to the line `AB` is at distance `r` from `P`. -/
def TangentToLine (P : Pt) (r : ℝ) (A B : Pt) : Prop :=
  ∃ s : ℝ, dist P (A + s • (B - A)) = r ∧ ⟪P - (A + s • (B - A)), B - A⟫ = 0

theorem tangentToLine_symm (P : Pt) (r : ℝ) (A B : Pt) (h : TangentToLine P r A B) :
    TangentToLine P r B A := by
  obtain ⟨s, hd, hperp⟩ := h
  refine ⟨1 - s, ?_, ?_⟩
  · rw [show B + (1 - s) • (A - B) = A + s • (B - A) by module]; exact hd
  · rw [show B + (1 - s) • (A - B) = A + s • (B - A) by module,
      show A - B = -(B - A) by module, inner_neg_right, hperp, neg_zero]

/-- If the circle with centre `P = A + β (B - A) + γ (C - A)` and radius `r` is tangent to the
line `AB`, then `r ‖B - A‖ = |γ| √(gram A B C)`; i.e. the distance from `P` to the line `AB` is
`|γ|` times the distance from `C` to that line. -/
theorem tangent_coeff (A B C P : Pt) (β γ r : ℝ) (hP : P = A + β • (B - A) + γ • (C - A))
    (h : TangentToLine P r A B) :
    r * ‖B - A‖ = |γ| * Real.sqrt (gram A B C) := by
  obtain ⟨s, hd, hperp⟩ := h
  set u := B - A with hu
  set v := C - A with hv
  have hPX : P - (A + s • u) = (β - s) • u + γ • v := by rw [hP]; module
  rw [hPX, inner_lin_comb] at hperp
  rw [dist_eq_norm, hPX] at hd
  have hr : r ^ 2 = (β - s) ^ 2 * ‖u‖ ^ 2 + 2 * (β - s) * γ * ⟪u, v⟫ + γ ^ 2 * ‖v‖ ^ 2 := by
    rw [← hd, norm_lin_comb_sq]
  have key : r ^ 2 * ‖u‖ ^ 2 = γ ^ 2 * gram A B C := by
    simp only [gram, ← hu, ← hv]
    nlinarith [hperp, hr]
  have hrn : 0 ≤ r := by rw [← hd]; positivity
  have hsq : r * ‖u‖ = Real.sqrt (r ^ 2 * ‖u‖ ^ 2) := by
    rw [show r ^ 2 * ‖u‖ ^ 2 = (r * ‖u‖) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [hsq, key, Real.sqrt_mul (sq_nonneg γ), Real.sqrt_sq_eq_abs]

/-- Tangency to the line `AB` pins down the barycentric coordinate of `P` opposite to `AB`. -/
theorem coeff_AB (A B C P : Pt) (α β γ r : ℝ) (hsum : α + β + γ = 1) (hγ : 0 ≤ γ)
    (hP : P = α • A + β • B + γ • C) (h : TangentToLine P r A B) :
    r * ‖B - A‖ = γ * Real.sqrt (gram A B C) := by
  have hα : α = 1 - β - γ := by linarith
  subst hα
  rw [tangent_coeff A B C P β γ r (by rw [hP]; module) h, abs_of_nonneg hγ]

/-- Tangency to the line `AC` pins down the barycentric coordinate of `P` opposite to `AC`. -/
theorem coeff_AC (A B C P : Pt) (α β γ r : ℝ) (hsum : α + β + γ = 1) (hβ : 0 ≤ β)
    (hP : P = α • A + β • B + γ • C) (h : TangentToLine P r A C) :
    r * ‖C - A‖ = β * Real.sqrt (gram A B C) := by
  have hα : α = 1 - β - γ := by linarith
  subst hα
  rw [tangent_coeff A C B P γ β r (by rw [hP]; module) h, abs_of_nonneg hβ, gram_swap]

/-- Tangency to the line `BC` pins down the barycentric coordinate of `P` opposite to `BC`. -/
theorem coeff_BC (A B C P : Pt) (α β γ r : ℝ) (hsum : α + β + γ = 1) (hα' : 0 ≤ α)
    (hP : P = α • A + β • B + γ • C) (h : TangentToLine P r B C) :
    r * ‖C - B‖ = α * Real.sqrt (gram A B C) := by
  have hβ : β = 1 - α - γ := by linarith
  subst hβ
  rw [tangent_coeff B C A P γ α r (by rw [hP]; module) h, abs_of_nonneg hα', gram_cycl]

/-! ### Barycentric coordinates -/

theorem exists_barycentric (A B C P : Pt) (h : P ∈ convexHull ℝ ({A, B, C} : Set Pt)) :
    ∃ α β γ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ α + β + γ = 1 ∧ P = α • A + β • B + γ • C := by
  rw [show ({A, B, C} : Set Pt) = insert A {B, C} from rfl, convexHull_insert (by simp),
    convexHull_pair, mem_convexJoin] at h
  obtain ⟨x, hx, z, hz, hP⟩ := h
  simp only [Set.mem_singleton_iff] at hx
  subst hx
  rw [segment_eq_image] at hz hP
  obtain ⟨b, hb, rfl⟩ := hz
  obtain ⟨a, ha, rfl⟩ := hP
  exact ⟨1 - a, a * (1 - b), a * b, by linarith [ha.1, ha.2], by nlinarith [ha.1, hb.1, hb.2],
    by nlinarith [ha.1, hb.1], by ring, by module⟩

/-! ### The incenter -/

/-- The incenter of the triangle `A B C`, given by its barycentric coordinates
`(a : b : c)` where `a = |BC|`, `b = |CA|`, `c = |AB|`. -/
noncomputable def incenter (A B C : Pt) : Pt :=
  (dist B C / (dist B C + dist C A + dist A B)) • A +
  (dist C A / (dist B C + dist C A + dist A B)) • B +
  (dist A B / (dist B C + dist C A + dist A B)) • C

/-! ### The main theorem -/
