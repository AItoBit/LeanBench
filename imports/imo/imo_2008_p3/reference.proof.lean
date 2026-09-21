by
  intro hfin
  obtain ⟨N, hN⟩ := hfin.bddAbove
  obtain ⟨p, hp, hpgt, hpmod⟩ :=
    Nat.exists_prime_gt_modEq_one (k := 4) (max 20 (N ^ 2 + 1)) (by norm_num)
  have hp4 : p % 4 = 1 := by
    have h := hpmod
    unfold Nat.ModEq at h
    omega
  have hp20 : 20 < p := lt_of_le_of_lt (le_max_left _ _) hpgt
  obtain ⟨n, hn0, hndvd, hreal⟩ := key p hp hp4 hp20
  have hmem : n ∈ {n : ℕ | 0 < n ∧ ∃ p : ℕ, p.Prime ∧ p ∣ n ^ 2 + 1 ∧
      (2 * (n : ℝ) + Real.sqrt (2 * (n : ℝ)) < p)} := ⟨hn0, p, hp, hndvd, hreal⟩
  have hnN : n ≤ N := hN hmem
  have h1 : p ≤ n ^ 2 + 1 := Nat.le_of_dvd (by positivity) hndvd
  have h2 : N ^ 2 + 1 < p := lt_of_le_of_lt (le_max_right _ _) hpgt
  nlinarith
