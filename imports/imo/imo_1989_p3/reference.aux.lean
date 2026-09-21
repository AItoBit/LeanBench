/-- Three points equidistant from two distinct points are collinear: they all lie on the
perpendicular bisector, a line. -/
theorem collinear_of_dist_eq {B C A₁ A₂ A₃ : Pt} (hBC : B ≠ C)
    (h₁ : dist A₁ B = dist A₁ C) (h₂ : dist A₂ B = dist A₂ C) (h₃ : dist A₃ B = dist A₃ C) :
    Collinear ℝ ({A₁, A₂, A₃} : Set Pt) := by
  have hsub : ({A₁, A₂, A₃} : Set Pt) ⊆ (AffineSubspace.perpBisector B C : Set Pt) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact AffineSubspace.mem_perpBisector_iff_dist_eq.2 h₁
    · exact AffineSubspace.mem_perpBisector_iff_dist_eq.2 h₂
    · exact AffineSubspace.mem_perpBisector_iff_dist_eq.2 h₃
  have hle : vectorSpan ℝ ({A₁, A₂, A₃} : Set Pt)
      ≤ (AffineSubspace.perpBisector B C).direction := by
    rw [← direction_affineSpan]
    exact AffineSubspace.direction_le (affineSpan_le.2 hsub)
  have hw : C -ᵥ B ≠ 0 := vsub_ne_zero.2 (Ne.symm hBC)
  have hdir : finrank ℝ (AffineSubspace.perpBisector B C).direction = 1 := by
    rw [AffineSubspace.direction_perpBisector]
    have h1 : finrank ℝ (ℝ ∙ (C -ᵥ B)) = 1 := finrank_span_singleton hw
    have h2 := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) (E := Pt) (ℝ ∙ (C -ᵥ B))
    rw [h1, finrank_euclideanSpace_fin] at h2
    omega
  rw [collinear_iff_finrank_le_one]
  calc finrank ℝ (vectorSpan ℝ ({A₁, A₂, A₃} : Set Pt))
      ≤ finrank ℝ (AffineSubspace.perpBisector B C).direction := Submodule.finrank_mono hle
    _ = 1 := hdir
