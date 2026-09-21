by
  have hpB : ∠ (t.points 0) (altitudeFoot t) (t.points 1) = π / 2 :=
    angle_self_orthogonalProjection _ (left_mem_affineSpan_pair ℝ _ _)
  have hpC : ∠ (t.points 0) (altitudeFoot t) (t.points 2) = π / 2 :=
    angle_self_orthogonalProjection _ (right_mem_affineSpan_pair ℝ _ _)
  have hcol : Collinear ℝ ({t.points 1, altitudeFoot t, t.points 2} : Set E) := by
    have hmem : altitudeFoot t ∈ line[ℝ, t.points 1, t.points 2] :=
      orthogonalProjection_mem _
    have h := collinear_insert_of_mem_affineSpan_pair hmem
    simpa only [Set.insert_comm] using h
  exact imo2001_p1_of_sbtw t (altitudeFoot t) hA hC
    (altitude_sbtw (t.independent.injective.ne (by decide : (1 : Fin 3) ≠ 2))
      hcol hB hC hpB hpC) hpC hgap
