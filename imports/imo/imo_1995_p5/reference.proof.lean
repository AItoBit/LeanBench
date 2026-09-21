by
  -- the triangles `BCD` and `EFA` are equilateral
  have hBD : dist B D = dist B C := by
    have hlaw := EuclideanGeometry.law_cos B C D
    rw [hangC, Real.cos_pi_div_three] at hlaw
    have hDC : dist D C = dist B C := by rw [dist_comm D C, ← hBC]
    rw [hDC] at hlaw
    nlinarith [hlaw, dist_nonneg (x := B) (y := D), dist_nonneg (x := B) (y := C)]
  have hEAeq : dist E A = dist E F := by
    have hlaw := EuclideanGeometry.law_cos E F A
    rw [hangF, Real.cos_pi_div_three] at hlaw
    have hAF : dist A F = dist E F := by rw [dist_comm A F, ← hEF]
    rw [hAF] at hlaw
    nlinarith [hlaw, dist_nonneg (x := E) (y := A), dist_nonneg (x := E) (y := F)]
  -- distance bookkeeping
  have hCB : dist C B = dist B D := by rw [hBD, dist_comm C B]
  have hCD : dist C D = dist B D := by rw [hBD, ← hBC]
  have hFE : dist F E = dist E A := by rw [hEAeq, dist_comm F E]
  have hFA : dist F A = dist E A := by rw [hEAeq, ← hEF]
  have hBA : dist B A = dist B D := by rw [hBD, dist_comm B A, hAB]
  have hED : dist E A = dist E D := by rw [hEAeq, dist_comm E D, hDE]
  rcases hconv with hccw | hcw
  · exact key_ccw A B C D E F G H hccw.2.1 hccw.2.2.2.2.1 hCB hCD hFE hFA hBA hED
  · -- reversed orientation: conjugate everything
    obtain ⟨-, -, hDCB, -, -, hAFE⟩ := hcw
    have hkey := key_ccw ((starRingEnd ℂ) A) ((starRingEnd ℂ) B) ((starRingEnd ℂ) C)
      ((starRingEnd ℂ) D) ((starRingEnd ℂ) E) ((starRingEnd ℂ) F) ((starRingEnd ℂ) G)
      ((starRingEnd ℂ) H)
      (ccw_conj hDCB) (ccw_conj hAFE)
      (by rw [dist_conj, dist_conj]; exact hCB) (by rw [dist_conj, dist_conj]; exact hCD)
      (by rw [dist_conj, dist_conj]; exact hFE) (by rw [dist_conj, dist_conj]; exact hFA)
      (by rw [dist_conj, dist_conj]; exact hBA) (by rw [dist_conj, dist_conj]; exact hED)
    simpa only [dist_conj] using hkey
