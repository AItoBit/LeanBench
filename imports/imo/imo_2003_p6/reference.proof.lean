by
  have hp2 : 2 ≤ p := hp.two_le
  have hp2sq : p + 2 ≤ p ^ 2 := by nlinarith
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = ∑ i ∈ Finset.range p, p ^ i := ⟨_, rfl⟩
  -- `N = 1 + p + p²M`
  obtain ⟨M, hM⟩ : ∃ M, N = 1 + p + p ^ 2 * M := by
    refine ⟨∑ i ∈ Finset.range (p - 2), p ^ i, ?_⟩
    obtain ⟨k, hk⟩ : ∃ k, p = k + 2 := ⟨p - 2, by omega⟩
    have hk2 : p - 2 = k := by omega
    rw [hNdef, hk2, hk]
    exact geom_split (k + 2) k
  have hN0 : N ≠ 0 := by omega
  -- `p ∤ N`
  have hpN : ¬ (p ∣ N) := by
    intro h
    rw [hM] at h
    have h5 : p ∣ p + p ^ 2 * M :=
      Dvd.dvd.add (dvd_refl p) (Dvd.dvd.mul_right (dvd_pow_self p two_ne_zero) M)
    have h4 : p ∣ p + p ^ 2 * M + 1 := by
      rwa [show p + p ^ 2 * M + 1 = 1 + p + p ^ 2 * M from by ring]
    have h6 : p ∣ 1 := (Nat.dvd_add_right h5).mp h4
    have := Nat.le_of_dvd one_pos h6
    omega
  -- a prime factor of `N` that is not `≡ 1 (mod p²)`
  obtain ⟨q, hq, hqN, hqne⟩ : ∃ q : ℕ, q.Prime ∧ q ∣ N ∧ ¬ (q ≡ 1 [MOD p ^ 2]) := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ x ∈ Nat.primeFactorsList N, x ≡ 1 [MOD p ^ 2] := fun x hx =>
      hcon x (Nat.prime_of_mem_primeFactorsList hx) (Nat.dvd_of_mem_primeFactorsList hx)
    have h1 := list_prod_modEq_one _ hall
    rw [Nat.prod_primeFactorsList hN0] at h1
    rw [Nat.ModEq, hM] at h1
    have h2 : (1 + p + p ^ 2 * M) % p ^ 2 = (1 + p) % p ^ 2 := by
      rw [show 1 + p + p ^ 2 * M = (1 + p) + p ^ 2 * M from by ring]
      exact Nat.add_mul_mod_self_left (1 + p) (p ^ 2) M
    rw [h2, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
    omega
  have hqp : q ≠ p := fun h => hpN (h ▸ hqN)
  haveI : Fact q.Prime := ⟨hq⟩
  -- `p^p = 1` in `ZMod q`
  have hgeom : (N : ℤ) * ((p : ℤ) - 1) = (p : ℤ) ^ p - 1 := by
    rw [hNdef]
    push_cast
    exact geom_sum_mul (p : ℤ) p
  have hppq : ((p : ZMod q)) ^ p = 1 := by
    have h1 : (q : ℤ) ∣ (p : ℤ) ^ p - 1 := by
      rw [← hgeom]
      exact Dvd.dvd.mul_right (Int.natCast_dvd_natCast.2 hqN) _
    have h2 : (((p : ℤ) ^ p - 1 : ℤ) : ZMod q) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h1
    push_cast at h2
    linear_combination h2
  have hpne0 : (p : ZMod q) ≠ 0 := by
    intro h
    have hdvd : q ∣ p := (ZMod.natCast_eq_zero_iff _ _).1 h
    exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).1 hdvd)
  refine ⟨q, hq, ?_⟩
  intro n hn
  have hxp : ((n : ZMod q)) ^ p = (p : ZMod q) := by
    have h1 : ((n ^ p - (p : ℤ) : ℤ) : ZMod q) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hn
    push_cast at h1
    linear_combination h1
  have hxne0 : (n : ZMod q) ≠ 0 := by
    intro h
    rw [h, zero_pow (by omega : p ≠ 0)] at hxp
    exact hpne0 hxp.symm
  -- the order of `n` divides `p²` and `q - 1`
  have hxp2 : ((n : ZMod q)) ^ (p ^ 2) = 1 := by
    rw [pow_two, pow_mul, hxp, hppq]
  have hord : orderOf ((n : ZMod q)) ∣ p ^ 2 := orderOf_dvd_of_pow_eq_one hxp2
  have hord2 : orderOf ((n : ZMod q)) ∣ q - 1 :=
    orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hxne0)
  have hnotp2 : orderOf ((n : ZMod q)) ≠ p ^ 2 := by
    intro h
    rw [h] at hord2
    exact hqne ((Nat.modEq_iff_dvd' hq.one_lt.le).2 hord2).symm
  -- so it divides `p`, and `p = 1` in `ZMod q`
  have hordp : orderOf ((n : ZMod q)) ∣ p := by
    obtain ⟨i, hi, hie⟩ := (Nat.dvd_prime_pow hp).1 hord
    rcases Nat.lt_or_ge i 2 with h | h
    · rw [hie]
      have h1 : p ^ i ∣ p ^ 1 := pow_dvd_pow p (by omega)
      rwa [pow_one] at h1
    · exfalso
      apply hnotp2
      rw [hie, show i = 2 from by omega]
  have hx1 : ((n : ZMod q)) ^ p = 1 := orderOf_dvd_iff_pow_eq_one.1 hordp
  have hp1 : (p : ZMod q) = 1 := by rw [← hxp, hx1]
  -- but `N` is both `0` and `1` in `ZMod q`
  have hN0q : (N : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hqN
  have hNq : (N : ZMod q) = 1 := by
    rw [hNdef]
    push_cast
    rw [hp1]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact hp1
  rw [hN0q] at hNq
  exact zero_ne_one hNq
