open Real

open scoped BigOperators

/-- Auxiliary lemma showing the cotangent double-angle identity:
    cot θ - cot 2θ = 1 / sin 2θ. -/
lemma cot_sub_cot_double (θ : ℝ) (h1 : sin θ ≠ 0) (h2 : sin (2 * θ) ≠ 0) :
    cos θ / sin θ - cos (2 * θ) / sin (2 * θ) = 1 / sin (2 * θ) := by
  have h_sub : sin (2 * θ) * cos θ - cos (2 * θ) * sin θ = sin θ := by
    have h_trig := sin_sub (2 * θ) θ
    have h_eq : 2 * θ - θ = θ := by ring
    rw [h_eq] at h_trig
    exact h_trig.symm
  have h_cancel : sin θ * sin (2 * θ) ≠ 0 := mul_ne_zero h1 h2
  have h_frac : cos θ / sin θ - cos (2 * θ) / sin (2 * θ) =
      (sin (2 * θ) * cos θ - cos (2 * θ) * sin θ) / (sin θ * sin (2 * θ)) := by
    field_simp
  rw [h_frac, h_sub]
  field_simp
