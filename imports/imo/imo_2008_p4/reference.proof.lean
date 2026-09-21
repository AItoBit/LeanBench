by
  constructor
  · intro hf
    by_cases hid : ∀ x : ℝ, 0 < x → f x = x
    · exact Or.inl hid
    · right
      push_neg at hid
      obtain ⟨b, hb, hbne⟩ := hid
      have hfb : f b = 1 / b := (pointwise f hpos hf b hb).resolve_left hbne
      have hb1 : b ≠ 1 := by
        rintro rfl
        exact hbne (by simpa using value_at_one f hpos hf)
      intro x hx
      rcases pointwise f hpos hf x hx with hc | hc
      · rcases no_mixing f hpos hf x b hx hb hc hfb with h1 | h1
        · rw [h1] at hc ⊢; norm_num [hc, h1]
        · exact absurd h1 hb1
      · exact hc
  · rintro (h | h) w x y z hw hx hy hz hcon
    · rw [h w hw, h x hx, h (y ^ 2) (by positivity), h (z ^ 2) (by positivity)]
    · rw [h w hw, h x hx, h (y ^ 2) (by positivity), h (z ^ 2) (by positivity)]
      have hw' : w ≠ 0 := ne_of_gt hw
      have hx' : x ≠ 0 := ne_of_gt hx
      have hy' : y ≠ 0 := ne_of_gt hy
      have hz' : z ≠ 0 := ne_of_gt hz
      have hyz : (0:ℝ) < y ^ 2 + z ^ 2 := by positivity
      have hwx : (0:ℝ) < w ^ 2 + x ^ 2 := by positivity
      have h2 : w ^ 2 * x ^ 2 = y ^ 2 * z ^ 2 := by rw [← mul_pow, ← mul_pow, hcon]
      rw [div_eq_div_iff (by positivity) (ne_of_gt hyz)]
      field_simp
      linear_combination (-(x ^ 2 + w ^ 2) * (y ^ 2 + z ^ 2)) * h2
