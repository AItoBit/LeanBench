by
  constructor
  · intro h
    -- `f` is injective
    have hinj : Function.Injective f := by
      intro u v huv
      have h1 := h 0 u
      have h2 := h 0 v
      rw [huv] at h1
      linarith
    -- a point sent to `0`
    obtain ⟨t, ht⟩ : ∃ t, f t = 0 := by
      refine ⟨f (-(f 0 ^ 2)), ?_⟩
      have h1 := h 0 (-(f 0 ^ 2))
      have h2 : (0 : ℝ) ^ 2 + f (-(f 0 ^ 2)) = f (-(f 0 ^ 2)) := by ring
      rw [h2] at h1
      linarith
    -- two equations for `t`
    have ht1 : t ^ 2 + f 0 = t := by
      refine hinj ?_
      have h1 := h t 0
      rw [ht] at h1
      rw [ht, h1]
      norm_num
    have ht2 : f 0 = t + (f 0) ^ 2 := by
      have h1 := h 0 t
      rw [ht] at h1
      have h2 : (0 : ℝ) ^ 2 + 0 = 0 := by ring
      rw [h2] at h1
      exact h1
    -- `f 0 = 0`
    have htv : t = f 0 - (f 0) ^ 2 := by linarith
    have hpoly : (f 0) ^ 2 * ((f 0 - 1) ^ 2 + 1) = 0 := by
      rw [htv] at ht1
      linear_combination ht1
    have hd0 : f 0 = 0 := by
      have hq : (0 : ℝ) < (f 0 - 1) ^ 2 + 1 := by positivity
      have hsq : (f 0) ^ 2 = 0 := by
        rcases mul_eq_zero.1 hpoly with h' | h'
        · exact h'
        · linarith
      exact sq_eq_zero_iff.mp hsq
    -- `f` is an involution
    have hff : ∀ y, f (f y) = y := by
      intro y
      have h1 := h 0 y
      rw [hd0] at h1
      have h2 : (0 : ℝ) ^ 2 + f y = f y := by ring
      rw [h2] at h1
      simpa using h1
    -- the shifted equation
    have hadd : ∀ x y : ℝ, f (x ^ 2 + y) = f y + (f x) ^ 2 := by
      intro x y
      have h1 := h x (f y)
      rw [hff y] at h1
      exact h1
    -- `f` is monotone
    have hmono : ∀ u v : ℝ, v ≤ u → f v ≤ f u := by
      intro u v huv
      have hs : Real.sqrt (u - v) ^ 2 = u - v := Real.sq_sqrt (by linarith)
      have h1 := hadd (Real.sqrt (u - v)) v
      rw [hs] at h1
      have h2 : u - v + v = u := by ring
      rw [h2] at h1
      nlinarith [sq_nonneg (f (Real.sqrt (u - v)))]
    -- conclude
    intro y
    rcases lt_trichotomy (f y) y with hlt | heq | hgt
    · exfalso
      have hge := hmono y (f y) hlt.le
      rw [hff y] at hge
      linarith
    · exact heq
    · exfalso
      have hle := hmono (f y) y hgt.le
      rw [hff y] at hle
      linarith
  · intro hf x y
    simp only [hf]
    ring
