namespace Imo1990P1

/-- If `M` lies strictly between `A` and `B` and `AM/AB = t`, then `0 < t < 1` and
`MA/MB = t/(1-t)`. -/
theorem ratio_of_sbtw {A M B : EuclideanSpace ℝ (Fin 2)} {t : ℝ}
    (h : Sbtw ℝ A M B) (ht : dist A M / dist A B = t) :
    0 < t ∧ t < 1 ∧ dist M A / dist M B = t / (1 - t) := by
  have hsum : dist A M + dist M B = dist A B := h.wbtw.dist_add_dist
  have hAM : 0 < dist A M := dist_pos.2 h.left_ne
  have hMB : 0 < dist M B := dist_pos.2 h.ne_right
  have hAB : 0 < dist A B := by linarith
  have hABne : dist A B ≠ 0 := hAB.ne'
  have hMBne : dist M B ≠ 0 := hMB.ne'
  have ht' : t = dist A M / dist A B := ht.symm
  have htpos : 0 < t := by rw [ht']; positivity
  have htlt : t < 1 := by
    rw [ht', div_lt_one hAB]
    linarith
  refine ⟨htpos, htlt, ?_⟩
  have h1t : 1 - t = dist M B / dist A B := by
    rw [ht']
    field_simp
    linarith
  rw [h1t, ht', dist_comm M A]
  field_simp

/-- The two similarity relations of Solution 1 give `EG/EF = MA/MB`. -/
theorem ratio_of_similar {MA MB EC MD EG EF : ℝ}
    (hMB : 0 < MB) (hEC : 0 < EC) (hEG : 0 < EG) (hEF : 0 < EF)
    (h₁ : MB / EC = MD / EG) (h₂ : MA / EC = MD / EF) :
    EG / EF = MA / MB := by
  have e₁ : MB * EG = MD * EC := (div_eq_div_iff hEC.ne' hEG.ne').1 h₁
  have e₂ : MA * EF = MD * EC := (div_eq_div_iff hEC.ne' hEF.ne').1 h₂
  rw [div_eq_div_iff hEF.ne' hMB.ne']
  linear_combination e₁ - e₂
