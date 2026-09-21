/-- **IMO 1992 P4.** The locus is the open ray of the line `r·x + m·y = m·r` above `y = r`. -/
theorem candidate (r m : ℝ) (hr : 0 < r) :
    {P : ℝ × ℝ | -r < P.2 ∧ ∃ q ρ : ℝ, q < 0 ∧ 0 < ρ ∧ q + ρ = 2 * m ∧
        OnTangent r q P.1 P.2 ∧ OnTangent r ρ P.1 P.2}
      = {P : ℝ × ℝ | r * P.1 + m * P.2 = m * r ∧ r < P.2} :=
