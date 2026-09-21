by
  have hUV : U ≠ V := by
    rintro rfl
    exact hXUV (by simp only [sdet]; ring)
  have habs : ∀ {P Q : ℝ × ℝ}, area P Q U = area P Q V →
      sdet P Q U = sdet P Q V ∨ sdet P Q U = -sdet P Q V := by
    intro P Q h
    exact abs_eq_abs.mp (by rw [abs_sdet_eq, abs_sdet_eq, h])
  have d₁ := habs h₁
  have d₂ := habs h₂
  have d₃ := habs h₃
  rcases d₁ with e₁ | e₁ <;> rcases d₂ with e₂ | e₂ <;> rcases d₃ with e₃ | e₃
  · -- all three pairs parallel to `UV`: use the pairs `XY`, `XZ`
    exact hXYZ (collinear_of_parallel hUV (by linarith) (by linarith))
  · exact hXYZ (collinear_of_parallel hUV (by linarith) (by linarith))
  · -- `XY` and `YZ` parallel to `UV`
    have key : sdet Y X Z = 0 :=
      collinear_of_parallel hUV
        (by simp only [sdet] at e₁ ⊢; linarith) (by linarith)
    exact hXYZ (by simp only [sdet] at key ⊢; linarith)
  · -- the midpoint of `UV` lies on `XZ` and on `YZ`
    have key : sdet Z X Y = 0 :=
      collinear_of_midpoint hZUV
        (by simp only [sdet] at e₂ ⊢; linarith) (by simp only [sdet] at e₃ ⊢; linarith)
    exact hXYZ (by simp only [sdet] at key ⊢; linarith)
  · -- `XZ` and `YZ` parallel to `UV`
    have key : sdet Z X Y = 0 :=
      collinear_of_parallel hUV
        (by simp only [sdet] at e₂ ⊢; linarith) (by simp only [sdet] at e₃ ⊢; linarith)
    exact hXYZ (by simp only [sdet] at key ⊢; linarith)
  · -- the midpoint of `UV` lies on `XY` and on `YZ`
    have key : sdet Y X Z = 0 :=
      collinear_of_midpoint hYUV
        (by simp only [sdet] at e₁ ⊢; linarith) (by linarith)
    exact hXYZ (by simp only [sdet] at key ⊢; linarith)
  · -- the midpoint of `UV` lies on `XY` and on `XZ`
    exact hXYZ (collinear_of_midpoint hXUV (by linarith) (by linarith))
  · exact hXYZ (collinear_of_midpoint hXUV (by linarith) (by linarith))
