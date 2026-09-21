by
  have hmy : my ≠ 0 := by
    intro hmy0
    have hfactor : mx * (mx - 1) = 0 := by
      rw [hmy0] at hMcircle
      simpa using hMcircle
    rcases mul_eq_zero.mp hfactor with hmx0 | hmx1
    · rw [hmx0, hmy0] at hMline
      apply ht
      linarith
    · have hmx : mx = 1 := by linarith
      exact hMneC (Prod.ext hmx hmy0)
  have hny : ny ≠ 0 := by
    intro hny0
    have hfactor : (nx - b) * (nx - d) = 0 := by
      rw [hny0] at hNcircle
      simpa using hNcircle
    rcases mul_eq_zero.mp hfactor with hnxB | hnxD
    · have hnx : nx = b := by linarith
      exact hNneB (Prod.ext hnx hny0)
    · have hnx : nx = d := by linarith
      rw [hnx, hny0] at hNline
      have hdb : 0 < d - b := by linarith
      apply ht
      nlinarith
  have hMrelation : mx * (z - 1) + t * my = 0 := by
    have hproduct : my * (mx * (z - 1) + t * my) = 0 := by
      linear_combination t * hMcircle - mx * hMline
    exact (mul_eq_zero.mp hproduct).resolve_left hmy
  have hNrelation : (z - b) * (nx - d) + t * ny = 0 := by
    have hproduct : ny * ((z - b) * (nx - d) + t * ny) = 0 := by
      linear_combination t * hNcircle - (nx - d) * hNline
    exact (mul_eq_zero.mp hproduct).resolve_left hny
  have hmx : mx ≠ 0 := by
    intro hmx0
    rw [hmx0] at hMrelation
    have htm : t * my = 0 := by simpa using hMrelation
    exact hmy (by
      apply (mul_eq_zero.mp htm).resolve_left ht)
  have hradical' : (z - d) * (z - b) - z * (z - 1) = 0 := by
    nlinarith [hradical]
  let q : ℝ := z * my / mx
  refine ⟨q, ?_, ?_⟩
  · dsimp [q]
    rw [div_mul_cancel₀ _ hmx]
    ring
  · have hpoly :
        mx * ((z - d) * ny) - z * my * (nx - d) = 0 := by
      have htpoly :
          t * (mx * ((z - d) * ny) - z * my * (nx - d)) = 0 := by
        linear_combination
          mx * (z - d) * hNrelation -
          z * (nx - d) * hMrelation -
          mx * (nx - d) * hradical'
      exact (mul_eq_zero.mp htpoly).resolve_left ht
    dsimp [q]
    field_simp [hmx]
    nlinarith
