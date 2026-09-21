by

  have hformula :
      ∀ i : ℕ, i < k → a i = a 0 + i * d := by
    intro i
    induction i with
    | zero =>
        intro _
        simp
    | succ i ih =>
        intro hi
        rw [hstep i hi, ih (by omega)]
        ring

  obtain ⟨i₁, hi₁, hai₁⟩ :=
    (hset 1).mp
      ⟨by omega, by omega, by simp⟩

  have hk : 0 < k := by
    omega

  have ha0pos : 0 < a 0 :=
    ((hset (a 0)).mpr ⟨0, hk, rfl⟩).1

  have hfirst : a 0 = 1 := by
    have h := hformula i₁ hi₁
    rw [hai₁] at h
    omega

  obtain ⟨j, hj, haj⟩ :=
    (hset (n - 1)).mp
      ⟨by omega, by omega,
        coprime_predecessor n (by omega)⟩

  have hend : n - 1 = 1 + j * d := by
    have h := hformula j hj
    rw [haj, hfirst] at h
    exact h

  apply classification_of_residue_progression n d hn hd
  intro r hr hrn
  constructor

  · intro hcop
    obtain ⟨i, hi, hai⟩ :=
      (hset r).mp ⟨hr, hrn, hcop⟩

    have hvalue : r = 1 + i * d := by
      have h := hformula i hi
      rw [hai, hfirst] at h
      exact h

    refine ⟨i, ?_⟩
    rw [Nat.mul_comm d i]
    omega

  · intro hdiv
    obtain ⟨i, hi⟩ := hdiv

    have hi' : r - 1 = i * d := by
      simpa only [Nat.mul_comm] using hi

    have hvalue : r = 1 + i * d := by
      omega

    have hik : i < k := by
      by_contra hnot
      have hji : j + 1 ≤ i := by
        omega
      have hmul : (j + 1) * d ≤ i * d :=
        Nat.mul_le_mul_right d hji
      rw [Nat.add_mul, Nat.one_mul] at hmul
      omega

    have hai : a i = r := by
      rw [hformula i hik, hfirst]
      exact hvalue.symm

    exact ((hset r).mpr ⟨i, hik, hai⟩).2.2
