by
  classical
  set g : ℕ := Nat.gcd p q with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ hp
  obtain ⟨p', hp'⟩ : g ∣ p := Nat.gcd_dvd_left p q
  obtain ⟨q', hq'⟩ : g ∣ q := Nat.gcd_dvd_right p q
  have hp'pos : 0 < p' := by
    rcases Nat.eq_zero_or_pos p' with h | h
    · rw [h, Nat.mul_zero] at hp'; omega
    · exact h
  have hq'pos : 0 < q' := by
    rcases Nat.eq_zero_or_pos q' with h | h
    · rw [h, Nat.mul_zero] at hq'; omega
    · exact h
  have hcop : Nat.Coprime p' q' := by
    have hc := Nat.coprime_div_gcd_div_gcd (m := p) (n := q) hgpos
    rw [← hg] at hc
    have h1 : p / g = p' := by
      rw [hp']
      exact Nat.mul_div_cancel_left _ hgpos
    have h2 : q / g = q' := by
      rw [hq']
      exact Nat.mul_div_cancel_left _ hgpos
    rwa [h1, h2] at hc
  have hsum' : p' + q' < n := by
    have : g * (p' + q') = p + q := by rw [hp', hq']; ring
    nlinarith [hgpos, hpq]
  -- every value is divisible by `g`
  have hdvdx : ∀ i, i ≤ n → (g : ℤ) ∣ x i := by
    intro i
    induction i with
    | zero => intro _; rw [h0]; exact dvd_zero _
    | succ i ih =>
      intro hle
      have h1 := ih (by omega)
      have h2 : (g : ℤ) ∣ (x (i + 1) - x i) := by
        rcases hstep i (by omega) with hs | hs
        · rw [hs, hp']; push_cast; exact Dvd.intro _ rfl
        · rw [hs, hq']; push_cast; exact ⟨-(q' : ℤ), by ring⟩
      have := dvd_add h2 h1
      simpa using this
  set y : ℕ → ℤ := fun i => x i / (g : ℤ) with hy
  have hgz : (g : ℤ) ≠ 0 := by exact_mod_cast hgpos.ne'
  have hxy : ∀ i, i ≤ n → x i = (g : ℤ) * y i := by
    intro i hle
    rw [hy]
    exact (Int.mul_ediv_cancel' (hdvdx i hle)).symm
  have hy0 : y 0 = 0 := by rw [hy]; simp [h0]
  have hyn : y n = 0 := by rw [hy]; simp [hn]
  have hystep : ∀ i, i < n → y (i + 1) - y i = (p' : ℤ) ∨ y (i + 1) - y i = -(q' : ℤ) := by
    intro i hlt
    have e1 := hxy (i + 1) (by omega)
    have e2 := hxy i (by omega)
    rcases hstep i hlt with hs | hs
    · left
      have : (g : ℤ) * (y (i + 1) - y i) = (g : ℤ) * (p' : ℤ) := by
        rw [mul_sub, ← e1, ← e2, hs, hp']; push_cast; ring
      exact mul_left_cancel₀ hgz this
    · right
      have : (g : ℤ) * (y (i + 1) - y i) = (g : ℤ) * (-(q' : ℤ)) := by
        rw [mul_sub, ← e1, ← e2, hs, hq']; push_cast; ring
      exact mul_left_cancel₀ hgz this
  obtain ⟨i, hile, hyeq⟩ := main p' q' n hp'pos hq'pos hsum' hcop y hy0 hyn hystep
  refine ⟨i, i + (p' + q'), by omega, hile, ?_, ?_⟩
  · rintro ⟨rfl, h2⟩
    omega
  · rw [hxy i (by omega), hxy (i + (p' + q')) hile, hyeq]
