/-- A solution of the functional equation satisfies `f 1 = 1`. -/
theorem value_at_one (f : ℝ → ℝ) (hpos : ∀ x : ℝ, 0 < x → 0 < f x) (hf : FE f) :
    f 1 = 1 := by
  have h1 : (0:ℝ) < f 1 := hpos 1 one_pos
  have h := hf 1 1 1 1 one_pos one_pos one_pos one_pos (by norm_num)
  norm_num at h
  have hne : f 1 + f 1 ≠ 0 := by positivity
  field_simp at h
  nlinarith [h, h1]

/-- Pointwise, a solution takes the value `x` or the value `1 / x`. -/
theorem pointwise (f : ℝ → ℝ) (hpos : ∀ x : ℝ, 0 < x → 0 < f x) (hf : FE f)
    (x : ℝ) (hx : 0 < x) : f x = x ∨ f x = 1 / x := by
  have h1 : f 1 = 1 := value_at_one f hpos hf
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  have h := hf 1 x (Real.sqrt x) (Real.sqrt x) one_pos hx hs hs (by
    rw [← sq, hsq]; ring)
  rw [hsq, h1] at h
  have hfx : 0 < f x := hpos x hx
  have hden : f x + f x ≠ 0 := by positivity
  have hden2 : x + x ≠ 0 := by positivity
  rw [div_eq_div_iff hden hden2] at h
  have hfac : (f x - x) * (x * f x - 1) = 0 := by nlinarith [h]
  rcases mul_eq_zero.mp hfac with h' | h'
  · left; linarith
  · right
    field_simp
    linarith [h']

/-- The two pointwise alternatives cannot be mixed. -/
theorem no_mixing (f : ℝ → ℝ) (hpos : ∀ x : ℝ, 0 < x → 0 < f x) (hf : FE f)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hfa : f a = a) (hfb : f b = 1 / b) :
    a = 1 ∨ b = 1 := by
  have hab : 0 < a * b := mul_pos ha hb
  have hs : 0 < Real.sqrt (a * b) := Real.sqrt_pos.mpr hab
  have hsq : Real.sqrt (a * b) ^ 2 = a * b := Real.sq_sqrt hab.le
  have h := hf a b (Real.sqrt (a * b)) (Real.sqrt (a * b)) ha hb hs hs (by
    rw [← sq, hsq])
  rw [hsq, hfa, hfb] at h
  have hfab : 0 < f (a * b) := hpos _ hab
  have hden : f (a * b) + f (a * b) ≠ 0 := by positivity
  have hden2 : a * b + a * b ≠ 0 := by positivity
  rw [div_eq_div_iff hden hden2] at h
  have hbne : b ≠ 0 := ne_of_gt hb
  have habne : a * b ≠ 0 := ne_of_gt hab
  rcases pointwise f hpos hf (a * b) hab with hc | hc
  · rw [hc] at h
    right
    have key : a ^ 2 + (1 / b) ^ 2 = a ^ 2 + b ^ 2 := mul_right_cancel₀ hden2 h
    have hb4 : b ^ 4 = 1 := by
      field_simp at key
      linarith [key]
    have hfac : (b - 1) * ((b + 1) * (b ^ 2 + 1)) = 0 := by linear_combination hb4
    rcases mul_eq_zero.mp hfac with h' | h'
    · linarith
    · nlinarith [h', hb]
  · rw [hc] at h
    left
    have ha4 : a ^ 4 = 1 := by
      field_simp at h
      have hb2 : b ^ 2 ≠ 0 := pow_ne_zero 2 hbne
      have hfac0 : (a ^ 4 - 1) * b ^ 2 = 0 := by linear_combination h
      rcases mul_eq_zero.mp hfac0 with h' | h'
      · linarith
      · exact absurd h' hb2
    have hfac : (a - 1) * ((a + 1) * (a ^ 2 + 1)) = 0 := by linear_combination ha4
    rcases mul_eq_zero.mp hfac with h' | h'
    · linarith
    · nlinarith [h', ha]
