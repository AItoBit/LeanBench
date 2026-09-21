by
  rcases A with ⟨ax, ay⟩
  rcases B with ⟨bx, bY⟩
  rcases C with ⟨cx, cy⟩
  rcases P with ⟨px, py⟩
  let s : ℝ := Real.sqrt 3
  have hs0 : 0 ≤ s := Real.sqrt_nonneg 3
  have hs2 : s ^ 2 = 3 := by
    dsimp [s]
    norm_num

  have hweitz_pos :
      2 * s * ((bx - ax) * (cy - ay) - (bY - ay) * (cx - ax)) ≤
        ((bx - ax) ^ 2 + (bY - ay) ^ 2) +
        ((cx - bx) ^ 2 + (cy - bY) ^ 2) +
        ((ax - cx) ^ 2 + (ay - cy) ^ 2) := by
    have hsq₁ :
        0 ≤ (2 * (bx - ax) - (cx - ax) - s * (cy - ay)) ^ 2 := sq_nonneg _
    have hsq₂ :
        0 ≤ (2 * (bY - ay) + s * (cx - ax) - (cy - ay)) ^ 2 := sq_nonneg _
    nlinarith

  have hweitz_neg :
      -(2 * s * ((bx - ax) * (cy - ay) - (bY - ay) * (cx - ax))) ≤
        ((bx - ax) ^ 2 + (bY - ay) ^ 2) +
        ((cx - bx) ^ 2 + (cy - bY) ^ 2) +
        ((ax - cx) ^ 2 + (ay - cy) ^ 2) := by
    have hsq₁ :
        0 ≤ (2 * (bx - ax) - (cx - ax) + s * (cy - ay)) ^ 2 := sq_nonneg _
    have hsq₂ :
        0 ≤ (2 * (bY - ay) - s * (cx - ax) - (cy - ay)) ^ 2 := sq_nonneg _
    nlinarith

  rcases hP with hccw | hcw
  · rcases hccw with ⟨hAB, hBC, hCA⟩
    by_contra h
    push_neg at h
    rcases h with ⟨h₁, h₂, h₃⟩
    unfold angleLE30 at h₁ h₂ h₃
    simp only [not_le] at h₁ h₂ h₃
    change s * |orient (ax, ay) (bx, bY) (px, py)| >
        dotAt (ax, ay) (bx, bY) (px, py) at h₁
    change s * |orient (bx, bY) (cx, cy) (px, py)| >
        dotAt (bx, bY) (cx, cy) (px, py) at h₂
    change s * |orient (cx, cy) (ax, ay) (px, py)| >
        dotAt (cx, cy) (ax, ay) (px, py) at h₃
    rw [abs_of_pos hAB] at h₁
    rw [abs_of_pos hBC] at h₂
    rw [abs_of_pos hCA] at h₃
    unfold orient dotAt at h₁ h₂ h₃
    nlinarith
  · rcases hcw with ⟨hAB, hBC, hCA⟩
    by_contra h
    push_neg at h
    rcases h with ⟨h₁, h₂, h₃⟩
    unfold angleLE30 at h₁ h₂ h₃
    simp only [not_le] at h₁ h₂ h₃
    change s * |orient (ax, ay) (bx, bY) (px, py)| >
        dotAt (ax, ay) (bx, bY) (px, py) at h₁
    change s * |orient (bx, bY) (cx, cy) (px, py)| >
        dotAt (bx, bY) (cx, cy) (px, py) at h₂
    change s * |orient (cx, cy) (ax, ay) (px, py)| >
        dotAt (cx, cy) (ax, ay) (px, py) at h₃
    rw [abs_of_neg hAB] at h₁
    rw [abs_of_neg hBC] at h₂
    rw [abs_of_neg hCA] at h₃
    unfold orient dotAt at h₁ h₂ h₃
    nlinarith
