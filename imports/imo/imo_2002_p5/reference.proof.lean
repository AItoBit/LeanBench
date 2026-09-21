by
  constructor
  · intro hf
    have hz := hf 0 0 0 0
    norm_num only [mul_zero, sub_zero, add_zero] at hz
    have hfactor : f 0 * (2 * f 0 - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfactor with h0 | hhalf
    · have hmul (x y : ℝ) : f (x * y) = f x * f y := by
        simpa [h0] using (hf x y 0 0).symm
      have hone := hmul 1 1
      simp only [one_mul] at hone
      have hfactor1 : f 1 * (f 1 - 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hfactor1 with h1 | h1
      · left
        funext x
        have h := hmul x 1
        simpa [h1] using h
      · right; right
        have h1' : f 1 = 1 := by linarith
        exact funext (normalized_square f hf h0 h1')
    · right; left
      have h0 : f 0 = 1 / 2 := by linarith
      funext x
      have h := hf x 0 0 0
      norm_num [h0] at h
      linarith
  · rintro (rfl | rfl | rfl)
    · intro x y z t
      norm_num
    · intro x y z t
      norm_num
    · intro x y z t
      dsimp
      ring
