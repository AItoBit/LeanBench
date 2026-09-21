by
  constructor
  · exact ⟨F, good_F, F_1998⟩
  · rintro v ⟨f, hf, rfl⟩
    have hk : 0 < f 1 := f_one_pos hf
    set g : ℕ → ℕ := fun t => f t / f 1 with hgdef
    have hfg : ∀ t, 0 < t → f t = f 1 * g t := fun t ht =>
      (Nat.mul_div_cancel' (k_dvd hf ht)).symm
    have hpos : ∀ n, 0 < n → 0 < g n := by
      intro n hn
      have h := hf.1 n hn
      rw [hfg n hn] at h
      exact Nat.pos_of_ne_zero fun h0 => by simp [h0] at h
    have hmul : ∀ a b, 0 < a → 0 < b → g (a * b) = g a * g b := by
      intro a b ha hb
      have h := k_mul_f_mul hf ha hb
      rw [hfg (a * b) (by positivity), hfg a ha, hfg b hb, ← mul_assoc] at h
      refine Nat.eq_of_mul_eq_mul_left (show 0 < f 1 * f 1 by positivity) ?_
      rw [h]; ring
    have hinv : ∀ a, 0 < a → g (g a) = a := by
      intro a ha
      have ha' : 0 < g a := hpos a ha
      have h1 : f (f a) = a * f 1 ^ 2 := ff hf ha
      rw [hfg a ha, f_k_mul hf ha', hfg (g a) ha', ← mul_assoc] at h1
      refine Nat.eq_of_mul_eq_mul_left (show 0 < f 1 * f 1 by positivity) ?_
      rw [h1]; ring
    have hg1 : g 1 = 1 := by
      refine Nat.eq_of_mul_eq_mul_left hk ?_
      rw [← hfg 1 one_pos, mul_one]
    calc (120 : ℕ) ≤ g 1998 := normalized_bound hpos hmul hinv hg1
      _ ≤ f 1 * g 1998 := Nat.le_mul_of_pos_left _ hk
      _ = f 1998 := (hfg 1998 (by norm_num)).symm
