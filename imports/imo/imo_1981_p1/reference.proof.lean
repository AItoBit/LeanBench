by
  have hgram : 0 < gram (B - A) (C - A) := gram_pos_of_not_collinear hABC
  obtain ⟨hu0, hv0, huv⟩ := gram_pos_ne hgram
  have hT : 0 < areaDoubled A B C := Real.sqrt_pos.mpr hgram
  have hapos : 0 < dist B C := dist_pos.mpr (fun h => huv (by rw [h]))
  have hbpos : 0 < dist C A := dist_pos.mpr (fun h => hv0 (by rw [h]; simp))
  have hcpos : 0 < dist A B := dist_pos.mpr (fun h => hu0 (by rw [← h]; simp))
  -- the three "area" identities
  have hx : dist P D * dist B C = α * areaDoubled A B C := by
    rw [dist_foot_mul P B C D hD hD', areaDoubled_rotate B P C, areaDoubled_swap P C B, hP,
      areaDoubled_comb A B C hsum hα.le]
  have hy : dist P E * dist C A = β * areaDoubled A B C := by
    have h1 := dist_foot_mul P C A E hE hE'
    rw [areaDoubled_rotate C P A, areaDoubled_swap P A C] at h1
    have hPcomb : P = β • B + γ • C + α • A := by rw [hP]; module
    have h2 : areaDoubled P C A = β * areaDoubled B C A := by
      rw [hPcomb, areaDoubled_comb B C A (by linarith) hβ.le]
    rw [h1, h2, areaDoubled_rotate A B C]
  have hz : dist P F * dist A B = γ * areaDoubled A B C := by
    have h1 := dist_foot_mul P A B F hF hF'
    rw [areaDoubled_rotate A P B, areaDoubled_swap P B A] at h1
    have hPcomb : P = γ • C + α • A + β • B := by rw [hP]; module
    have h2 : areaDoubled P A B = γ * areaDoubled C A B := by
      rw [hPcomb, areaDoubled_comb C A B (by linarith) hγ.le]
    rw [h1, h2, areaDoubled_rotate A B C, areaDoubled_rotate B C A]
  have hxpos : 0 < dist P D := by
    nlinarith [dist_nonneg (x := P) (y := D), mul_pos hα hT]
  have hypos : 0 < dist P E := by
    nlinarith [dist_nonneg (x := P) (y := E), mul_pos hβ hT]
  have hzpos : 0 < dist P F := by
    nlinarith [dist_nonneg (x := P) (y := F), mul_pos hγ hT]
  have hsum2 : dist B C * dist P D + dist C A * dist P E + dist A B * dist P F
      = areaDoubled A B C := by
    linear_combination hx + hy + hz + areaDoubled A B C * hsum
  obtain ⟨hle, hiff⟩ := min_lemma hapos hbpos hcpos hxpos hypos hzpos hsum2
  refine ⟨hle, hiff.trans ⟨?_, ?_⟩, hiff⟩
  · -- equal distances to the three sides force `P` to be the incenter
    rintro ⟨hxy, hyz⟩
    have hy' : dist P E * dist C A = β * areaDoubled A B C := hy
    rw [← hxy] at hy'
    have hz' : dist P F * dist A B = γ * areaDoubled A B C := hz
    rw [← hyz, ← hxy] at hz'
    have hsumr : dist P D * (dist B C + dist C A + dist A B) = areaDoubled A B C := by
      linear_combination hx + hy' + hz' + areaDoubled A B C * hsum
    have e1 : (dist B C + dist C A + dist A B) * α = dist B C :=
      mul_left_cancel₀ (ne_of_gt hT)
        (by linear_combination (-(dist B C + dist C A + dist A B)) * hx + dist B C * hsumr)
    have e2 : (dist B C + dist C A + dist A B) * β = dist C A :=
      mul_left_cancel₀ (ne_of_gt hT)
        (by linear_combination (-(dist B C + dist C A + dist A B)) * hy' + dist C A * hsumr)
    have e3 : (dist B C + dist C A + dist A B) * γ = dist A B :=
      mul_left_cancel₀ (ne_of_gt hT)
        (by linear_combination (-(dist B C + dist C A + dist A B)) * hz' + dist A B * hsumr)
    rw [hP, smul_add, smul_add, smul_smul, smul_smul, smul_smul, e1, e2, e3]
  · -- conversely, the incenter is equidistant from the three sides
    intro hkey
    have hα3 : α = 1 - β - γ := by linarith
    have expand : ((dist B C + dist C A + dist A B) * β - dist C A) • (B - A)
        + ((dist B C + dist C A + dist A B) * γ - dist A B) • (C - A)
        = (dist B C + dist C A + dist A B) • P
          - (dist B C • A + dist C A • B + dist A B • C) := by
      rw [hP, hα3]; module
    have hzero : ((dist B C + dist C A + dist A B) * β - dist C A) • (B - A)
        + ((dist B C + dist C A + dist A B) * γ - dist A B) • (C - A) = 0 := by
      rw [expand, hkey, sub_self]
    obtain ⟨hb', hc'⟩ := eq_zero_of_gram_pos hgram hzero
    have ha' : (dist B C + dist C A + dist A B) * α = dist B C := by
      linear_combination (dist B C + dist C A + dist A B) * hsum - hb' - hc'
    have hb'' : (dist B C + dist C A + dist A B) * β = dist C A := by linarith
    have hc'' : (dist B C + dist C A + dist A B) * γ = dist A B := by linarith
    have hs : 0 < dist B C + dist C A + dist A B := by linarith
    have hxs : dist P D * (dist B C + dist C A + dist A B) = areaDoubled A B C :=
      mul_left_cancel₀ (ne_of_gt hα) (by linear_combination hx + dist P D * ha')
    have hys : dist P E * (dist B C + dist C A + dist A B) = areaDoubled A B C :=
      mul_left_cancel₀ (ne_of_gt hβ) (by linear_combination hy + dist P E * hb'')
    have hzs : dist P F * (dist B C + dist C A + dist A B) = areaDoubled A B C :=
      mul_left_cancel₀ (ne_of_gt hγ) (by linear_combination hz + dist P F * hc'')
    exact ⟨mul_right_cancel₀ (ne_of_gt hs) (by rw [hxs, hys]),
      mul_right_cancel₀ (ne_of_gt hs) (by rw [hys, hzs])⟩
