namespace EqualAreaLabelling

/-- Twice the signed area of the triangle `P Q R`. -/
def sdet (P Q R : ℝ × ℝ) : ℝ :=
  (Q.1 - P.1) * (R.2 - P.2) - (Q.2 - P.2) * (R.1 - P.1)

/-- The (unsigned) area of the triangle `P Q R`. -/
noncomputable def area (P Q R : ℝ × ℝ) : ℝ := |sdet P Q R| / 2

theorem sdet_swap12 (P Q R : ℝ × ℝ) : sdet Q P R = -sdet P Q R := by
  simp only [sdet]; ring

theorem sdet_swap13 (P Q R : ℝ × ℝ) : sdet R Q P = -sdet P Q R := by
  simp only [sdet]; ring

theorem sdet_swap23 (P Q R : ℝ × ℝ) : sdet P R Q = -sdet P Q R := by
  simp only [sdet]; ring

/-- The alternating sum of the four signed areas determined by four points
vanishes. -/
theorem sdet_alternating (P Q R S : ℝ × ℝ) :
    sdet Q R S - sdet P R S + sdet P Q S - sdet P Q R = 0 := by
  simp only [sdet]; ring

theorem area_nonneg (P Q R : ℝ × ℝ) : 0 ≤ area P Q R := by
  simp only [area]
  positivity

theorem area_pos {P Q R : ℝ × ℝ} (h : sdet P Q R ≠ 0) : 0 < area P Q R := by
  simp only [area]
  have : 0 < |sdet P Q R| := abs_pos.mpr h
  linarith

theorem abs_sdet_eq {P Q R : ℝ × ℝ} : |sdet P Q R| = 2 * area P Q R := by
  simp only [area]; ring

/-- Two vectors both parallel to a nonzero vector are parallel. -/
theorem cross_trans {p₁ p₂ q₁ q₂ w₁ w₂ : ℝ} (hw : ¬(w₁ = 0 ∧ w₂ = 0))
    (h₁ : p₁ * w₂ - p₂ * w₁ = 0) (h₂ : q₁ * w₂ - q₂ * w₁ = 0) :
    p₁ * q₂ - p₂ * q₁ = 0 := by
  have e₁ : (p₁ * q₂ - p₂ * q₁) * w₁ = 0 := by linear_combination q₁ * h₁ - p₁ * h₂
  have e₂ : (p₁ * q₂ - p₂ * q₁) * w₂ = 0 := by linear_combination q₂ * h₁ - p₂ * h₂
  by_cases hw₁ : w₁ = 0
  · have hw₂ : w₂ ≠ 0 := fun h => hw ⟨hw₁, h⟩
    exact (mul_eq_zero.mp e₂).resolve_right hw₂
  · exact (mul_eq_zero.mp e₁).resolve_right hw₁

/-- If `U ≠ V` and both `XY` and `XZ` are parallel to `UV`, then `X`, `Y`, `Z`
are collinear. -/
theorem collinear_of_parallel {X Y Z U V : ℝ × ℝ} (hUV : U ≠ V)
    (h₁ : sdet X Y U - sdet X Y V = 0) (h₂ : sdet X Z U - sdet X Z V = 0) :
    sdet X Y Z = 0 := by
  have hw : ¬(U.1 - V.1 = 0 ∧ U.2 - V.2 = 0) := by
    rintro ⟨a, b⟩
    exact hUV (Prod.ext (by linarith) (by linarith))
  have key := cross_trans (p₁ := Y.1 - X.1) (p₂ := Y.2 - X.2)
    (q₁ := Z.1 - X.1) (q₂ := Z.2 - X.2) (w₁ := U.1 - V.1) (w₂ := U.2 - V.2) hw
    (by simp only [sdet] at h₁ ⊢; linarith [h₁]) (by simp only [sdet] at h₂ ⊢; linarith [h₂])
  simp only [sdet]
  linarith [key]

/-- If the midpoint of `UV` lies on both line `XY` and line `XZ`, then either
`X`, `U`, `V` are collinear (the midpoint is `X`) or `X`, `Y`, `Z` are
collinear. -/
theorem collinear_of_midpoint {X Y Z U V : ℝ × ℝ} (hX : sdet X U V ≠ 0)
    (h₁ : sdet X Y U + sdet X Y V = 0) (h₂ : sdet X Z U + sdet X Z V = 0) :
    sdet X Y Z = 0 := by
  have hw : ¬(U.1 + V.1 - 2 * X.1 = 0 ∧ U.2 + V.2 - 2 * X.2 = 0) := by
    rintro ⟨a, b⟩
    exact hX (by
      simp only [sdet]
      linear_combination (U.1 - X.1) * b - (U.2 - X.2) * a)
  have key := cross_trans (p₁ := Y.1 - X.1) (p₂ := Y.2 - X.2)
    (q₁ := Z.1 - X.1) (q₂ := Z.2 - X.2)
    (w₁ := U.1 + V.1 - 2 * X.1) (w₂ := U.2 + V.2 - 2 * X.2) hw
    (by simp only [sdet] at h₁ ⊢; linarith [h₁]) (by simp only [sdet] at h₂ ⊢; linarith [h₂])
  simp only [sdet]
  linarith [key]
