namespace Imo2006P1

open EuclideanGeometry Module Real

open scoped Affine

section Oriented

variable {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
  [NormedAddTorsor V Pt] [Fact (finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

/-! ### Generic lemmas on oriented and unoriented angles -/

/-- An angle whose oriented version has nonzero sign is strictly between `0` and `π`. -/
lemma angle_pos_lt_pi_of_oangle_sign_ne_zero {p p₁ p₂ : Pt} (h : (∡ p₁ p p₂).sign ≠ 0) :
    0 < ∠ p₁ p p₂ ∧ ∠ p₁ p p₂ < π := by
  rw [Real.Angle.sign_ne_zero_iff] at h
  have h1 : p₁ ≠ p := left_ne_of_oangle_ne_zero h.1
  have h2 : p₂ ≠ p := right_ne_of_oangle_ne_zero h.1
  refine ⟨?_, ?_⟩
  · rcases (angle_nonneg p₁ p p₂).lt_or_eq with h' | h'
    · exact h'
    · exact absurd ((oangle_eq_zero_iff_angle_eq_zero h1 h2).2 h'.symm) h.1
  · rcases (angle_le_pi p₁ p p₂).lt_or_eq with h' | h'
    · exact h'
    · exact absurd (oangle_eq_pi_iff_angle_eq_pi.2 h') h.2

/-- Unoriented angles add when the corresponding oriented angles all have the same nonzero
sign. -/
lemma angle_add_angle_of_oangle_sign_eq {p p₁ p₂ p₃ : Pt}
    (h₁ : (∡ p₁ p p₂).sign = (∡ p₁ p p₃).sign)
    (h₂ : (∡ p₂ p p₃).sign = (∡ p₁ p p₃).sign)
    (h₀ : (∡ p₁ p p₃).sign ≠ 0) :
    ∠ p₁ p p₂ + ∠ p₂ p p₃ = ∠ p₁ p p₃ := by
  have hne1 : p₁ ≠ p := left_ne_of_oangle_sign_ne_zero (h₁ ▸ h₀)
  have hne2 : p₂ ≠ p := right_ne_of_oangle_sign_ne_zero (h₁ ▸ h₀)
  have hne3 : p₃ ≠ p := right_ne_of_oangle_sign_ne_zero h₀
  have hadd : ∡ p₁ p p₂ + ∡ p₂ p p₃ = ∡ p₁ p p₃ := oangle_add hne1 hne2 hne3
  obtain ⟨b1, b1'⟩ := angle_pos_lt_pi_of_oangle_sign_ne_zero (h₁ ▸ h₀ : (∡ p₁ p p₂).sign ≠ 0)
  obtain ⟨b2, b2'⟩ := angle_pos_lt_pi_of_oangle_sign_ne_zero (h₂ ▸ h₀ : (∡ p₂ p p₃).sign ≠ 0)
  obtain ⟨b3, b3'⟩ := angle_pos_lt_pi_of_oangle_sign_ne_zero h₀
  have key : ((∠ p₁ p p₂ + ∠ p₂ p p₃ : ℝ) : Real.Angle) = ((∠ p₁ p p₃ : ℝ) : Real.Angle) := by
    rw [Real.Angle.coe_add]
    rcases hs : (∡ p₁ p p₃).sign with _ | _ | _
    · exact absurd hs h₀
    · rw [oangle_eq_neg_angle_of_sign_eq_neg_one (h₁.trans hs),
        oangle_eq_neg_angle_of_sign_eq_neg_one (h₂.trans hs),
        oangle_eq_neg_angle_of_sign_eq_neg_one hs, ← neg_add, neg_inj] at hadd
      exact hadd
    · rw [oangle_eq_angle_of_sign_eq_one (h₁.trans hs), oangle_eq_angle_of_sign_eq_one (h₂.trans hs),
        oangle_eq_angle_of_sign_eq_one hs] at hadd
      exact hadd
  rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub] at key
  obtain ⟨k, hk⟩ := key
  have hpi := Real.pi_pos
  have hk0 : k = 0 := by
    rcases lt_trichotomy k 0 with h | h | h
    · have hk1 : k ≤ -1 := by omega
      have : (k : ℝ) ≤ -1 := by exact_mod_cast hk1
      nlinarith
    · exact h
    · have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h
      nlinarith
  rw [hk0] at hk
  push_cast at hk
  linarith
