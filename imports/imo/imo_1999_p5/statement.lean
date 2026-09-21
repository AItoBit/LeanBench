/-- **Metric core of IMO 1999 P5.** The distance from the centre of `G₂` to the line `CD` is
exactly the radius of `G₂`. -/
theorem candidate (R r₁ r₂ t s : ℝ) (O₁ O₂ n X : ℂ)
    (hR : 0 < R) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hn : ‖n‖ = 1)
    (h1 : ‖O₁‖ = R - r₁)
    (h2 : ‖O₂‖ = R - r₂)
    (h12 : O₂ - O₁ = (r₁ : ℂ) * n)
    (hXt : dot X n = t)
    (hXrad : ‖X - O₁‖ ^ 2 - r₁ ^ 2 = ‖X - O₂‖ ^ 2 - r₂ ^ 2)
    (hhom : dot O₁ n - s = (r₁ / R) * (0 - t)) :
    |dot O₂ n - s| = r₂ :=
