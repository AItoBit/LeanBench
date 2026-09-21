by
  -- the elimination identity
  have key :
      ((x - u) ^ 2 + (y - v) ^ 2)
        * (r ^ 2 * (x * y - u * v) + x * y * (v ^ 2 - u ^ 2) + u * v * (x ^ 2 - y ^ 2)) * s
      = (r ^ 2 * (x - u) ^ 2 + (x * v - y * u) ^ 2)
        * ((x ^ 2 + y ^ 2 - r ^ 2) * v - (u ^ 2 + v ^ 2 - r ^ 2) * y) := by
    linear_combination
      (-x * y * (-r ^ 2 * u + r ^ 2 * x + u ^ 3 - u ^ 2 * x + u * v ^ 2 - 2 * u * v * y
        + v ^ 2 * x)) * h1
      + ((x ^ 2 - y ^ 2 - r ^ 2) * (-r ^ 2 * u + r ^ 2 * x + u ^ 3 - u ^ 2 * x + u * v ^ 2
        - 2 * u * v * y + v ^ 2 * x) / 2) * h2
      + (u * v * (r ^ 2 * u - r ^ 2 * x - u * x ^ 2 + u * y ^ 2 - 2 * v * x * y + x ^ 3
        + x * y ^ 2)) * h3
      + (-(u ^ 2 - v ^ 2 - r ^ 2) * (r ^ 2 * u - r ^ 2 * x - u * x ^ 2 + u * y ^ 2
        - 2 * v * x * y + x ^ 3 + x * y ^ 2) / 2) * h4
  -- `K ≠ 0`, from the bisecting hypothesis
  have hKne : r ^ 2 * (x - u) ^ 2 + (x * v - y * u) ^ 2 ≠ 0 := by
    intro h0
    have hA : r ^ 2 * (x - u) ^ 2 = 0 := by nlinarith [sq_nonneg (x - u), sq_nonneg (x * v - y * u)]
    have hB : (x * v - y * u) ^ 2 = 0 := by nlinarith [sq_nonneg (x - u), sq_nonneg (x * v - y * u)]
    have hxu : x = u := by nlinarith [sq_nonneg (x - u)]
    have hxv : x * v - y * u = 0 := by nlinarith [hB]
    have hx0 : x * (v - y) = 0 := by rw [hxu]; linarith [hxv, hxu]
    rcases mul_eq_zero.1 hx0 with h | h
    · exact hK ⟨h, by rw [← hxu]; exact h⟩
    · apply hbd
      have hvy : v = y := by linarith
      rw [hxu, hvy]
      ring
  constructor
  · intro hs
    have hsr : s * r = 0 := by nlinarith [hs]
    have hs0 : s = 0 := by
      rcases mul_eq_zero.1 hsr with h | h
      · exact h
      · exact absurd h (ne_of_gt hr)
    rw [hs0, mul_zero] at key
    have h5 := (mul_eq_zero.1 key.symm).resolve_left hKne
    linarith
  · intro hcyc
    have hcyc0 : (x ^ 2 + y ^ 2 - r ^ 2) * v - (u ^ 2 + v ^ 2 - r ^ 2) * y = 0 := by linarith
    rw [hcyc0, mul_zero] at key
    have h5 := (mul_eq_zero.1 key).resolve_left (mul_ne_zero hbd hE)
    rw [h5]
    ring
