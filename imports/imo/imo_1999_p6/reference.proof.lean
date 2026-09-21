by
  constructor
  · intro P
    -- `f 0 ≠ 0`
    have hc : f 0 ≠ 0 := by
      intro h
      have h1 := P 0 0
      simp [h] at h1
    -- the formula on the range of `f`
    have hrange : ∀ y : ℝ, f (f y) = (f 0 + 1 - (f y) ^ 2) / 2 := by
      intro y
      have h1 := P (f y) y
      rw [sub_self] at h1
      have hsq : (f y) ^ 2 = f y * f y := pow_two _
      linarith
    -- the formula on differences of values
    have hdiff : ∀ y z : ℝ, f (f z - f y) = f 0 - (f z - f y) ^ 2 / 2 := by
      intro y z
      have h1 := P (f z) y
      rw [hrange y, hrange z] at h1
      rw [h1]
      ring
    -- every real is such a difference
    have hsurj : ∀ w : ℝ, ∃ y z : ℝ, f z - f y = w := by
      intro w
      refine ⟨(w - f (f 0) + 1) / f 0, (w - f (f 0) + 1) / f 0 - f 0, ?_⟩
      have h1 := P ((w - f (f 0) + 1) / f 0) 0
      have hxf : ((w - f (f 0) + 1) / f 0) * f 0 = w - f (f 0) + 1 := by
        field_simp
      rw [h1]
      linarith
    -- hence the formula everywhere
    have hform : ∀ w : ℝ, f w = f 0 - w ^ 2 / 2 := by
      intro w
      obtain ⟨y, z, hyz⟩ := hsurj w
      have h1 := hdiff y z
      rw [hyz] at h1
      exact h1
    -- and `f 0 = 1`
    have hc1 : f 0 = 1 := by
      have h1 := hrange 0
      have h2 := hform (f 0)
      rw [h2] at h1
      linarith
    intro x
    rw [hform x, hc1]
  · intro hf x y
    simp only [hf]
    ring
