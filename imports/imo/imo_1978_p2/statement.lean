/-- The same statement as a distance: `Q` lies on the sphere of centre `O` and
radius `√(3R² − 2·OP²)`. -/
theorem candidate (O P A B C Q : V) (R : ℝ)
    (hA : dist A O = R) (hB : dist B O = R) (hC : dist C O = R)
    (hab : ⟪A - P, B - P⟫ = 0) (hbc : ⟪B - P, C - P⟫ = 0) (hca : ⟪C - P, A - P⟫ = 0)
    (hQ : Q = P + (A - P) + (B - P) + (C - P)) :
    dist Q O = Real.sqrt (3 * R ^ 2 - 2 * dist P O ^ 2) :=
