/-- The computation, in inner-product form. -/
private lemma key (p u v w : V) (R : ℝ)
    (hu : ⟪p + u, p + u⟫ = R ^ 2) (hv : ⟪p + v, p + v⟫ = R ^ 2)
    (hw : ⟪p + w, p + w⟫ = R ^ 2)
    (huv : ⟪u, v⟫ = 0) (hvw : ⟪v, w⟫ = 0) (hwu : ⟪w, u⟫ = 0) :
    ⟪p + u + v + w, p + u + v + w⟫ = 3 * R ^ 2 - 2 * ⟪p, p⟫ := by
  simp only [inner_add_left, inner_add_right] at hu hv hw ⊢
  linarith [real_inner_comm p u, real_inner_comm p v, real_inner_comm p w,
    real_inner_comm u v, real_inner_comm v w, real_inner_comm w u]

/-- **IMO 1978, Problem 2** (forward half).  With `A, B, C` on the sphere of
centre `O` and radius `R`, the segments `PA, PB, PC` pairwise perpendicular and
`Q` the opposite vertex of the parallelepiped, `OQ² = 3R² − 2·OP²`. -/
theorem imo1978_p2 (O P A B C Q : V) (R : ℝ)
    (hA : dist A O = R) (hB : dist B O = R) (hC : dist C O = R)
    (hab : ⟪A - P, B - P⟫ = 0) (hbc : ⟪B - P, C - P⟫ = 0) (hca : ⟪C - P, A - P⟫ = 0)
    (hQ : Q = P + (A - P) + (B - P) + (C - P)) :
    dist Q O ^ 2 = 3 * R ^ 2 - 2 * dist P O ^ 2 := by
  have e1 : A - O = (P - O) + (A - P) := by abel
  have e2 : B - O = (P - O) + (B - P) := by abel
  have e3 : C - O = (P - O) + (C - P) := by abel
  have e4 : Q - O = (P - O) + (A - P) + (B - P) + (C - P) := by rw [hQ]; abel
  have hu : ⟪(P - O) + (A - P), (P - O) + (A - P)⟫ = R ^ 2 := by
    rw [← e1, real_inner_self_eq_norm_sq, ← dist_eq_norm, hA]
  have hv : ⟪(P - O) + (B - P), (P - O) + (B - P)⟫ = R ^ 2 := by
    rw [← e2, real_inner_self_eq_norm_sq, ← dist_eq_norm, hB]
  have hw : ⟪(P - O) + (C - P), (P - O) + (C - P)⟫ = R ^ 2 := by
    rw [← e3, real_inner_self_eq_norm_sq, ← dist_eq_norm, hC]
  have hmain := key (P - O) (A - P) (B - P) (C - P) R hu hv hw hab hbc hca
  rw [dist_eq_norm, dist_eq_norm, ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq, e4]
  exact hmain
