/-- **Metric core of IMO 1990 P1.** With the two similarities of Solution 1 as hypotheses,
`EG/EF = t/(1-t)`. -/
theorem candidate {A B C D E F G M : EuclideanSpace ℝ (Fin 2)} {t : ℝ}
    (hM : Sbtw ℝ A M B) (ht : dist A M / dist A B = t)
    (hEC : 0 < dist E C) (hEG : 0 < dist E G) (hEF : 0 < dist E F)
    -- `△CEG ∼ △BMD`
    (h₁ : dist M B / dist E C = dist M D / dist E G)
    -- `△CEF ∼ △AMD`
    (h₂ : dist M A / dist E C = dist M D / dist E F) :
    dist E G / dist E F = t / (1 - t) :=
