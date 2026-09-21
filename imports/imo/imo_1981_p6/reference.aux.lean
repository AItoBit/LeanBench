/-- `f 1 y = y + 2`. -/
theorem f_one (y : ℕ) : f 1 y = y + 2 := by
  induction y with
  | zero =>
      have e : f 1 0 = f 0 1 := h2 0
      rw [e, h1]
  | succ y ih =>
      have e : f 1 (y + 1) = f 0 (f 1 y) := h3 0 y
      rw [e, h1, ih]

/-- `f 2 y = 2 * y + 3`. -/
theorem f_two (y : ℕ) : f 2 y = 2 * y + 3 := by
  induction y with
  | zero =>
      have e : f 2 0 = f 1 1 := h2 1
      rw [e, f_one f h1 h2 h3]
  | succ y ih =>
      have e : f 2 (y + 1) = f 1 (f 2 y) := h3 1 y
      rw [e, f_one f h1 h2 h3, ih]
      ring

/-- `f 3 y + 3 = 2 ^ (y + 3)`. -/
theorem f_three (y : ℕ) : f 3 y + 3 = 2 ^ (y + 3) := by
  induction y with
  | zero =>
      have e : f 3 0 = f 2 1 := h2 2
      rw [e, f_two f h1 h2 h3]
      norm_num
  | succ y ih =>
      have e : f 3 (y + 1) = f 2 (f 3 y) := h3 2 y
      have hp : (2 : ℕ) ^ (y + 1 + 3) = 2 * 2 ^ (y + 3) := by ring
      rw [e, f_two f h1 h2 h3]
      omega

/-- `f 4 y + 3 = tower (y + 3)`. -/
theorem f_four (y : ℕ) : f 4 y + 3 = tower (y + 3) := by
  induction y with
  | zero =>
      have e : f 4 0 = f 3 1 := h2 3
      have h := f_three f h1 h2 h3 1
      rw [e]
      norm_num [tower] at h ⊢
      omega
  | succ y ih =>
      have e : f 4 (y + 1) = f 3 (f 4 y) := h3 3 y
      have h := f_three f h1 h2 h3 (f 4 y)
      have ht : tower (y + 1 + 3) = 2 ^ tower (y + 3) := rfl
      rw [e, h, ht, ih]
