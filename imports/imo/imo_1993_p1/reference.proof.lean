by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hsub : m + 2 - 1 = m + 1 := by omega
  rw [hsub]
  rintro ⟨g, h, hg, hh, hgh⟩
  have hgh' : g * h = f m := hgh
  have hhg' : h * g = f m := by rw [mul_comm]; exact hgh'
  have hconst : g.coeff 0 * h.coeff 0 = 3 := by
    rw [← f_coeff_zero m, ← hgh', Polynomial.mul_coeff_zero]
  have hnotboth : ¬ ((3 : ℤ) ∣ g.coeff 0) ∨ ¬ ((3 : ℤ) ∣ h.coeff 0) := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hcon
    rw [ha, hb] at hconst
    obtain ⟨c, hc⟩ : ∃ c : ℤ, 9 * c = 3 := ⟨a * b, by linear_combination hconst⟩
    omega
  have hone : g.natDegree = 1 ∨ h.natDegree = 1 := by
    rcases hnotboth with hc | hc
    · have hle : g.natDegree ≤ 1 := natDegree_le_one_of_not_dvd m h g hhg' hc
      exact Or.inl (le_antisymm hle hg)
    · have hle : h.natDegree ≤ 1 := natDegree_le_one_of_not_dvd m g h hgh' hc
      exact Or.inr (le_antisymm hle hh)
  have hroot : ∃ r : ℤ, (f m).eval r = 0 := by
    have key : ∀ p q : ℤ[X], p * q = f m → q.natDegree = 1 → ∃ r : ℤ, (f m).eval r = 0 := by
      intro p q hpq hq1
      have hlead : p.leadingCoeff * q.leadingCoeff = 1 := by
        have hl := congrArg Polynomial.leadingCoeff hpq
        rwa [Polynomial.leadingCoeff_mul, (f_monic m).leadingCoeff] at hl
      have hdvd1 : q.leadingCoeff ∣ 1 := ⟨p.leadingCoeff, by rw [← hlead]; ring⟩
      have hu : IsUnit q.leadingCoeff := isUnit_of_dvd_one hdvd1
      have hlq : q.leadingCoeff = q.coeff 1 := by
        rw [Polynomial.leadingCoeff, hq1]
      have hsq : q.coeff 1 * q.coeff 1 = 1 := by
        rcases Int.isUnit_iff.1 hu with h1 | h1 <;> rw [hlq] at h1 <;> rw [h1] <;> norm_num
      have hdeg1 : q.degree ≤ 1 := by
        have hd := Polynomial.degree_le_natDegree (p := q)
        rw [hq1] at hd
        exact_mod_cast hd
      have hqform : q = C (q.coeff 1) * X + C (q.coeff 0) :=
        Polynomial.eq_X_add_C_of_degree_le_one hdeg1
      -- abstract the two coefficients, so that rewriting `q` cannot touch the root
      obtain ⟨a, b, hq_eq, ha1⟩ : ∃ a b : ℤ, q = C a * X + C b ∧ a * a = 1 :=
        ⟨q.coeff 1, q.coeff 0, hqform, hsq⟩
      refine ⟨-(a * b), ?_⟩
      rw [← hpq, Polynomial.eval_mul]
      have hq0 : q.eval (-(a * b)) = 0 := by
        rw [hq_eq]
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_X]
        linear_combination (-b) * ha1
      rw [hq0, mul_zero]
    rcases hone with h1 | h1
    · exact key h g hhg' h1
    · exact key g h hgh' h1
  obtain ⟨r, hr⟩ := hroot
  exact f_no_root m r hr
