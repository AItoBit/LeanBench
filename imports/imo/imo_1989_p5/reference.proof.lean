by
  refine ⟨(Nat.factorial (n + 1)) ^ 2 + 2, by positivity, ?_⟩
  intro i hi
  -- `k = 2 + i` divides `(n+1)!`
  obtain ⟨d, hd⟩ : (2 + i) ∣ Nat.factorial (n + 1) :=
    Nat.dvd_factorial (by omega) (by omega)
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | h
    · rw [mul_zero] at hd
      exact absurd hd (Nat.factorial_pos (n + 1)).ne'
    · exact h
  -- the factorisation `N + k = k (k d² + 1)`
  have hfac : (Nat.factorial (n + 1)) ^ 2 + 2 + i = (2 + i) * ((2 + i) * d ^ 2 + 1) := by
    rw [hd]; ring
  -- the two prime factors
  have hkne : (2 + i) ≠ 1 := by omega
  have hcne : (2 + i) * d ^ 2 + 1 ≠ 1 := by
    have h1 : 0 < (2 + i) * d ^ 2 := Nat.mul_pos (by omega) (pow_pos hd0 2)
    omega
  have hpp : ((2 + i).minFac).Prime := Nat.minFac_prime hkne
  have hqp : (((2 + i) * d ^ 2 + 1).minFac).Prime := Nat.minFac_prime hcne
  have hne : (2 + i).minFac ≠ ((2 + i) * d ^ 2 + 1).minFac := by
    intro h
    have h1 : ((2 + i) * d ^ 2 + 1).minFac ∣ (2 + i) := h ▸ Nat.minFac_dvd (2 + i)
    have h2 : ((2 + i) * d ^ 2 + 1).minFac ∣ (2 + i) * d ^ 2 + 1 := Nat.minFac_dvd _
    have h3 : ((2 + i) * d ^ 2 + 1).minFac ∣ (2 + i) * d ^ 2 := h1.mul_right _
    exact hqp.ne_one (Nat.dvd_one.mp ((Nat.dvd_add_right h3).mp h2))
  refine not_isPrimePow_of_two_primes hpp hqp hne ?_ ?_
  · rw [hfac]; exact (Nat.minFac_dvd _).mul_right _
  · rw [hfac]; exact (Nat.minFac_dvd _).mul_left _
