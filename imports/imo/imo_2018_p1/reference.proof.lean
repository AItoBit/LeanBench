by
  have hD1 : D.1 = A.1 + l * (B.1 - A.1) := by rw [hD]; simp
  have hD2 : D.2 = A.2 + l * (B.2 - A.2) := by rw [hD]; simp
  have hE1 : E.1 = A.1 + m * (C.1 - A.1) := by rw [hE]; simp
  have hE2 : E.2 = A.2 + m * (C.2 - A.2) := by rw [hE]; simp
  -- The two squared side lengths are positive.
  have hp : 0 < dotp (B - A) (B - A) := by
    rcases (show (0:ℝ) ≤ dotp (B - A) (B - A) by
        simp only [dotp, Prod.fst_sub, Prod.snd_sub]
        nlinarith [sq_nonneg (B.1 - A.1), sq_nonneg (B.2 - A.2)]).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hABC
      have hx : (B.1 - A.1) ^ 2 + (B.2 - A.2) ^ 2 = 0 := by
        simp only [dotp, Prod.fst_sub, Prod.snd_sub] at h
        linear_combination -h
      have h2 := (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).mp hx
      have hb1 : B.1 - A.1 = 0 := by
        have := h2.1; exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      have hb2 : B.2 - A.2 = 0 := by
        have := h2.2; exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      simp only [crossp, Prod.fst_sub, Prod.snd_sub]
      linear_combination (C.2 - A.2) * hb1 - (C.1 - A.1) * hb2
  have hq : 0 < dotp (C - A) (C - A) := by
    rcases (show (0:ℝ) ≤ dotp (C - A) (C - A) by
        simp only [dotp, Prod.fst_sub, Prod.snd_sub]
        nlinarith [sq_nonneg (C.1 - A.1), sq_nonneg (C.2 - A.2)]).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hABC
      have hx : (C.1 - A.1) ^ 2 + (C.2 - A.2) ^ 2 = 0 := by
        simp only [dotp, Prod.fst_sub, Prod.snd_sub] at h
        linear_combination -h
      have h2 := (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).mp hx
      have hc1 : C.1 - A.1 = 0 := by
        have := h2.1; exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      have hc2 : C.2 - A.2 = 0 := by
        have := h2.2; exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      simp only [crossp, Prod.fst_sub, Prod.snd_sub]
      linear_combination (B.1 - A.1) * hc2 - (B.2 - A.2) * hc1
  -- `2 A·P + |P|² = 0` and its analogue for `Q`.
  have hAP : dotp (A - O) (B - A) = -(dotp (B - A) (B - A)) / 2 := by
    simp only [dotp, Prod.fst_sub, Prod.snd_sub] at hA hB ⊢
    linear_combination (hB - hA) / 2
  have hAQ : dotp (A - O) (C - A) = -(dotp (C - A) (C - A)) / 2 := by
    simp only [dotp, Prod.fst_sub, Prod.snd_sub] at hA hC ⊢
    linear_combination (hC - hA) / 2
  -- The perpendicular-bisector conditions, cleaned up.
  have hFP : dotp (F - O) (B - A) = l * dotp (B - A) (B - A) / 2 := by
    have hne : l - 1 ≠ 0 := ne_of_lt (by linarith)
    have key : (l - 1) * (2 * dotp (F - O) (B - A) - l * dotp (B - A) (B - A)) = 0 := by
      simp only [dotp, Prod.fst_sub, Prod.snd_sub] at hA hB hFbd ⊢
      rw [hD1, hD2] at hFbd
      linear_combination hFbd + (1 - l) * hA - (1 - l) * hB
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h hne
    · linarith
  have hGQ : dotp (G - O) (C - A) = m * dotp (C - A) (C - A) / 2 := by
    have hne : m - 1 ≠ 0 := ne_of_lt (by linarith)
    have key : (m - 1) * (2 * dotp (G - O) (C - A) - m * dotp (C - A) (C - A)) = 0 := by
      simp only [dotp, Prod.fst_sub, Prod.snd_sub] at hA hC hGce ⊢
      rw [hE1, hE2] at hGce
      linear_combination hGce + (1 - m) * hA - (1 - m) * hC
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h hne
    · linarith
  -- `AD = AE`.
  have hS : l ^ 2 * dotp (B - A) (B - A) = m ^ 2 * dotp (C - A) (C - A) := by
    simp only [dotp, Prod.fst_sub, Prod.snd_sub] at hDE ⊢
    rw [hD1, hD2, hE1, hE2] at hDE
    linear_combination hDE
  -- Lagrange gives the four square identities.
  have hX2 : crossp (B - A) (F - O) ^ 2
      = dotp (B - A) (B - A) * R ^ 2 - l ^ 2 * dotp (B - A) (B - A) ^ 2 / 4 := by
    have h := lagrange (F - O) (B - A)
    rw [hFc, hFP] at h
    linear_combination -h
  have hY2 : crossp (C - A) (G - O) ^ 2
      = dotp (C - A) (C - A) * R ^ 2 - m ^ 2 * dotp (C - A) (C - A) ^ 2 / 4 := by
    have h := lagrange (G - O) (C - A)
    rw [hGc, hGQ] at h
    linear_combination -h
  have hk2 : crossp (B - A) (A - O) ^ 2
      = dotp (B - A) (B - A) * R ^ 2 - dotp (B - A) (B - A) ^ 2 / 4 := by
    have h := lagrange (A - O) (B - A)
    rw [hA, hAP] at h
    linear_combination -h
  have hk'2 : crossp (C - A) (A - O) ^ 2
      = dotp (C - A) (C - A) * R ^ 2 - dotp (C - A) (C - A) ^ 2 / 4 := by
    have h := lagrange (A - O) (C - A)
    rw [hA, hAQ] at h
    linear_combination -h
  -- Rewrite the two arc hypotheses in terms of `X, Y, k, k'`.
  have hcrossFA : crossp (B - A) (F - A)
      = crossp (B - A) (F - O) - crossp (B - A) (A - O) := by
    simp only [crossp, Prod.fst_sub, Prod.snd_sub]; ring
  have hcrossGA : crossp (C - A) (G - A)
      = crossp (C - A) (G - O) - crossp (C - A) (A - O) := by
    simp only [crossp, Prod.fst_sub, Prod.snd_sub]; ring
  have hCBA : crossp (C - A) (B - A) = -crossp (B - A) (C - A) := by
    simp only [crossp, Prod.fst_sub, Prod.snd_sub]; ring
  rw [hcrossFA] at harcF
  rw [hcrossGA, hCBA] at harcG
  have harcG' : 0 < (crossp (C - A) (G - O) - crossp (C - A) (A - O))
      * crossp (B - A) (C - A) := by nlinarith [harcG]
  -- The scalar core.
  obtain ⟨hMY, hMX⟩ := core hp hq hl0 hl1 hm0 hm1 hS hX2 hY2 hk2 hk'2 hABC harcF harcG'
  -- Resolve `F` along `(P, Pᗮ)` and `G` along `(Q, Qᗮ)`.
  have hn : dotp (C - A) (B - A) = dotp (B - A) (C - A) := by
    simp only [dotp, Prod.fst_sub, Prod.snd_sub]; ring
  have e1 : dotp (B - A) (B - A) * crossp (C - A) (F - O)
      = l * dotp (B - A) (B - A) / 2 * -crossp (B - A) (C - A)
        + crossp (B - A) (F - O) * dotp (B - A) (C - A) := by
    have h := cross_decomp (F - O) (B - A) (C - A)
    rw [hFP, hCBA, hn] at h
    exact h
  have e2 : dotp (C - A) (C - A) * crossp (B - A) (G - O)
      = m * dotp (C - A) (C - A) / 2 * crossp (B - A) (C - A)
        + crossp (C - A) (G - O) * dotp (B - A) (C - A) := by
    have h := cross_decomp (G - O) (C - A) (B - A)
    rw [hGQ] at h
    exact h
  -- Expand the goal and finish.
  have expand : crossp (E - D) (G - F)
      = m * crossp (C - A) (G - O) - m * crossp (C - A) (F - O)
        - l * crossp (B - A) (G - O) + l * crossp (B - A) (F - O) := by
    simp only [crossp, Prod.fst_sub, Prod.snd_sub]
    rw [hD1, hD2, hE1, hE2]
    ring
  have final : dotp (B - A) (B - A) * dotp (C - A) (C - A) * crossp (E - D) (G - F) = 0 := by
    rw [expand]
    linear_combination (dotp (B - A) (B - A) * dotp (C - A) (C - A)) * hMY
      - (m * dotp (C - A) (C - A)) * e1 - (l * dotp (B - A) (B - A)) * e2
      - dotp (B - A) (C - A) * hMX
  rcases mul_eq_zero.mp final with h | h
  · exact absurd h (ne_of_gt (mul_pos hp hq))
  · exact h
