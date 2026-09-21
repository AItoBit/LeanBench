private lemma K_zero : K 0 = 3 := rfl

private lemma Q_zero : Q 0 = 1 := rfl

private lemma f_def (n : ℕ) : f n = 2 ^ K n - 3 := rfl

private lemma Q_succ (n : ℕ) : Q (n + 1) = Q n * f n := rfl

private lemma K_succ (n : ℕ) : K (n + 1) = (K n + 1) * Nat.totient (Q (n + 1)) := rfl

/-- The invariant carried along the construction. -/
private lemma inv (n : ℕ) : 3 ≤ K n ∧ 0 < Q n ∧ ¬ (2 ∣ Q n) := by
  induction n with
  | zero => refine ⟨by norm_num [K_zero], by norm_num [Q_zero], by norm_num [Q_zero]⟩
  | succ m ih =>
    obtain ⟨hK, hQ, hQ2⟩ := ih
    have hx : 8 ≤ 2 ^ K m := by
      calc (8 : ℕ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ K m := Nat.pow_le_pow_right (by norm_num) hK
    have hxe : (2 : ℕ) ∣ 2 ^ K m := dvd_pow_self 2 (by omega)
    have hfdef : f m = 2 ^ K m - 3 := f_def m
    have hf5 : 5 ≤ f m := by omega
    have hf2 : ¬ (2 ∣ f m) := by omega
    have hQ' : 0 < Q (m + 1) := by
      rw [Q_succ]; exact Nat.mul_pos hQ (by omega)
    have hQ2' : ¬ (2 ∣ Q (m + 1)) := by
      rw [Q_succ]
      intro hcon
      rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hcon with h | h
      · exact hQ2 h
      · exact hf2 h
    have hphi : 0 < Nat.totient (Q (m + 1)) := Nat.totient_pos.mpr hQ'
    refine ⟨?_, hQ', hQ2'⟩
    rw [K_succ]
    have h4 : 4 * 1 ≤ (K m + 1) * Nat.totient (Q (m + 1)) :=
      Nat.mul_le_mul (by omega) hphi
    omega

private lemma eight_le (n : ℕ) : 8 ≤ 2 ^ K n := by
  calc (8 : ℕ) = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ K n := Nat.pow_le_pow_right (by norm_num) (inv n).1

private lemma five_le_f (n : ℕ) : 5 ≤ f n := by
  have h := eight_le n
  have hfdef : f n = 2 ^ K n - 3 := f_def n
  omega

/-- Each new term is coprime to the whole product of the previous ones. -/
private lemma coprime_f_Q (n : ℕ) : Nat.Coprime (f n) (Q n) := by
  cases n with
  | zero => rw [Q_zero]; exact Nat.coprime_one_right _
  | succ m =>
    obtain ⟨hK, hQ, hQ2⟩ := inv (m + 1)
    -- Euler: `2 ^ φ (Q (m+1)) ≡ 1 [MOD Q (m+1)]`.
    have hc2 : Nat.Coprime 2 (Q (m + 1)) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hQ2
    have hmod : (2 : ℕ) ^ Nat.totient (Q (m + 1)) ≡ 1 [MOD Q (m + 1)] :=
      Nat.ModEq.pow_totient hc2
    -- and `φ (Q (m+1)) ∣ K (m+1)`, so `2 ^ K (m+1) ≡ 1 [MOD Q (m+1)]`.
    have hmod2 : (2 : ℕ) ^ K (m + 1) ≡ 1 [MOD Q (m + 1)] := by
      rw [K_succ, Nat.mul_comm, pow_mul]
      simpa using hmod.pow (K m + 1)
    have hx8 : 8 ≤ 2 ^ K (m + 1) := eight_le (m + 1)
    -- Any common divisor of `f (m+1)` and `Q (m+1)` divides `2`, hence is `1`.
    have key : ∀ d : ℕ, d ∣ f (m + 1) → d ∣ Q (m + 1) → d = 1 := by
      intro d hd1 hd2
      have hmodd : (2 : ℕ) ^ K (m + 1) ≡ 1 [MOD d] := Nat.ModEq.of_dvd hd2 hmod2
      have hdvd1 : d ∣ 2 ^ K (m + 1) - 1 :=
        (Nat.modEq_iff_dvd' (by omega)).mp hmodd.symm
      have hdvd2 : d ∣ 2 ^ K (m + 1) - 3 := hd1
      have hd2' : d ∣ 2 := by
        -- `Nat.dvd_sub'` no longer exists; cancel the common summand instead.
        have heq : 2 ^ K (m + 1) - 1 = (2 ^ K (m + 1) - 3) + 2 := by omega
        rw [heq] at hdvd1
        exact (Nat.dvd_add_right hdvd2).mp hdvd1
      rcases (Nat.dvd_prime Nat.prime_two).mp hd2' with h1 | h1
      · exact h1
      · subst h1; exact absurd hd2 hQ2
    exact key _ (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)

private lemma Q_dvd_Q : ∀ i j : ℕ, i ≤ j → Q i ∣ Q j := by
  intro i j
  induction j with
  | zero =>
    intro h
    rw [Nat.le_zero.mp h]
  | succ m ih =>
    intro h
    rcases Nat.eq_or_lt_of_le h with h' | h'
    · rw [h']
    · exact (ih (by omega)).trans ⟨f m, Q_succ m⟩

private lemma f_dvd_Q {i j : ℕ} (h : i < j) : f i ∣ Q j := by
  -- the type ascription must be on a `have`, otherwise the anonymous
  -- constructor stays an `Exists` and `.trans` resolves to `Exists.trans`.
  have h1 : f i ∣ Q (i + 1) := ⟨Q i, by rw [Q_succ i, Nat.mul_comm]⟩
  exact h1.trans (Q_dvd_Q _ _ h)

private lemma coprime_lt {i j : ℕ} (h : i < j) : Nat.Coprime (f i) (f j) :=
  (Nat.Coprime.coprime_dvd_right (f_dvd_Q h) (coprime_f_Q j)).symm

private lemma f_ne {i j : ℕ} (h : i < j) : f i ≠ f j := by
  intro hij
  have hc := coprime_lt h
  rw [hij] at hc
  have h1 : Nat.gcd (f j) (f j) = 1 := hc
  rw [Nat.gcd_self] at h1
  have h5 := five_le_f j
  omega

private lemma f_inj : Function.Injective f := by
  intro i j hij
  by_contra hne
  rcases Nat.lt_or_ge i j with h | h
  · exact f_ne h hij
  · exact f_ne (by omega : j < i) hij.symm
