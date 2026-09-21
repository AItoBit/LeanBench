by
  subst hm1 hm2 hn1 hn2 hr1 hr2
  have hbc : 0 < b + c := by linarith
  -- `K` is interior to `BC`
  have hk1 : -1 < k := by
    have h1 : (k + 1) * (b + c) = 2 * b := by linear_combination hk
    nlinarith [hb, hbc]
  have hk2 : k < 1 := by
    have h1 : (1 - k) * (b + c) = 2 * c := by linear_combination -hk
    nlinarith [hc, hbc]
  -- the bisector condition, cleared of square roots
  have hbc2 : b * (1 - k) = c * (1 + k) := by linear_combination -hk
  have hsq : b ^ 2 * (1 - k) ^ 2 = c ^ 2 * (1 + k) ^ 2 := by
    linear_combination (b * (1 - k) + c * (1 + k)) * hbc2
  have hbis : u * (1 + k ^ 2) = k * (u ^ 2 + v ^ 2 + 1) := by
    linear_combination (1 / 4) * hsq - ((1 - k) ^ 2 / 4) * hbsq + ((1 + k) ^ 2 / 4) * hcsq
  -- both feet realise the power of `A`
  have hs : s * ((1 - u) ^ 2 + v ^ 2) = u ^ 2 + v ^ 2 - 1 := by linear_combination hMperp
  have ht : t' * ((u + 1) ^ 2 + v ^ 2) = u ^ 2 + v ^ 2 - 1 := by linear_combination hNperp
  -- and so does `R` on the bisector
  have hgoal : t * ((k - u) ^ 2 + v ^ 2) = u ^ 2 + v ^ 2 - 1 := by
    have h0 : (4 * (u ^ 2 + v ^ 2 - 1) * u) *
        (t * ((k - u) ^ 2 + v ^ 2) - (u ^ 2 + v ^ 2 - 1)) = 0 := by
      linear_combination
        (-(((u + 1) ^ 2 + v ^ 2) * ((1 - u) ^ 2 + v ^ 2))) * hReq
        + (-(((u + 1) ^ 2 + v ^ 2) *
            (-((1 - u) ^ 2 + v ^ 2) * s + 2 * t * (k * (1 - u) + u ^ 2 - u + v ^ 2)
              - (u ^ 2 + v ^ 2 - 1)))) * hs
        + (-(((1 - u) ^ 2 + v ^ 2) *
            (((u + 1) ^ 2 + v ^ 2) * t' + 2 * t * (k * (1 + u) - u ^ 2 - u - v ^ 2)
              + (u ^ 2 + v ^ 2 - 1)))) * ht
        + (4 * (u ^ 2 + v ^ 2 - 1) * t) * hbis
    have hne : (4 * (u ^ 2 + v ^ 2 - 1) * u) ≠ 0 :=
      mul_ne_zero (by linarith) hu
    have h1 := (mul_eq_zero.1 h0).resolve_left hne
    linarith
  refine ⟨?_, ?_, hk1, hk2⟩
  · exact cyc_of_pow_eq u v 1 0 k 0 _ _ _ _ s t (by ring) (by ring) (by ring) (by ring)
      (by linear_combination hs - hgoal)
  · exact cyc_of_pow_eq u v (-1) 0 k 0 _ _ _ _ t' t (by ring) (by ring) (by ring) (by ring)
      (by linear_combination ht - hgoal)
