lemma natDegree_numerpol : (X ^ m + X - 1 : ℤ[X]).natDegree = m := by
  compute_degree <;> grind

lemma monic_numerpol : (X ^ m + X - 1 : ℤ[X]).Monic := by
  apply Monic.sub_of_left
  · apply monic_X_pow_add
    rw [degree_X, Nat.one_lt_cast]
    lia
  · rw [degree_one, degree_add_eq_left_of_degree_lt]
    · simp_rw [degree_X_pow, Nat.cast_pos]
      lia
    · rw [degree_X_pow, degree_X, Nat.one_lt_cast]
      lia

lemma natDegree_denompol : (X ^ n + X ^ 2 - 1 : ℤ[X]).natDegree = n := by
  compute_degree <;> grind

lemma monic_denompol : (X ^ n + X ^ 2 - 1 : ℤ[X]).Monic := by
  apply Monic.sub_of_left
  · apply monic_X_pow_add
    rw [degree_X_pow, Nat.cast_lt]
    lia
  · rw [degree_one, degree_add_eq_left_of_degree_lt]
    · simp_rw [degree_X_pow, Nat.cast_pos]
      lia
    · simp_rw [degree_X_pow, Nat.cast_lt]
      lia

lemma proof_body (h : {a : ℤ | 0 < a ∧ a ^ n + a ^ 2 - 1 ∣ a ^ m + a - 1}.Infinite) :
    m = 5 ∧ n = 3 := by
  replace h : (X ^ n + X ^ 2 - 1 : ℤ[X]) ∣ X ^ m + X - 1 :=
    dvd_of_infinite_eval_dvd_eval (monic_denompol hn) (h.mono (by simp))
  -- Algebraic part: `n ≤ m - n + 1`
  have db := natDegree_le_of_dvd h (monic_numerpol hm).ne_zero
  rw [natDegree_numerpol hm, natDegree_denompol hn] at db
  replace h := dvd_sub_self_right.mpr (dvd_mul_of_dvd_left h (X + 1))
  have rearr : ((X ^ m + X - 1) * (X + 1) - (X ^ n + X ^ 2 - 1) : ℤ[X]) =
      X ^ n * (X ^ (m - n + 1) + X ^ (m - n) - 1) := by
    nth_rw 1 [← Nat.sub_add_cancel db]
    ring
  rw [rearr] at h
  replace h : (X ^ n + X ^ 2 - 1 : ℤ[X]) ∣ X ^ (m - n + 1) + X ^ (m - n) - 1 := by
    refine (IsRelPrime.pow_right ?_).dvd_of_dvd_mul_left h
    nth_rw 1 [isRelPrime_comm, irreducible_X.isRelPrime_iff_not_dvd,
      show (X : ℤ[X]) = X - C 0 by simp, dvd_iff_isRoot]
    simp [show n ≠ 0 by lia]
  have de : (X ^ (m - n + 1) + X ^ (m - n) - 1 : ℤ[X]).natDegree = m - n + 1 := by
    compute_degree <;> lia
  have db₂ := natDegree_le_of_dvd h (ne_zero_of_natDegree_gt (n := 0) (by lia))
  rw [natDegree_denompol hn, de] at db₂
  -- Analytic part: given the above, `m - n ≤ 2`
  suffices m - n ≤ 2 by lia
  let hom := Int.castRingHom ℝ
  obtain ⟨r, br, hr⟩ : ∃ r ∈ Set.Ioo 0 1, (X ^ n + X ^ 2 - 1 : ℤ[X]).eval₂ hom r = 0 := by
    simp only [eval₂_sub, eval₂_add, eval₂_X_pow, eval₂_one]
    let f (r : ℝ) := r ^ n + r ^ 2 - 1
    have cf : ContinuousOn f (Set.Icc 0 1) := by fun_prop
    have ivt := intermediate_value_Ioo zero_le_one cf
    have f0 : f 0 = -1 := by simp [f]; lia
    have f1 : f 1 = 1 := by simp [f]
    rw [f0, f1] at ivt
    simpa using ivt (by simp)
  have hr₂ := eval₂_dvd hom r h
  simp only [eval₂_sub, eval₂_add, eval₂_X_pow, eval₂_one] at hr hr₂
  rw [hr, zero_dvd_iff, ← hr, sub_left_inj] at hr₂
  rw [← pow_le_pow_iff_right_of_lt_one₀ br.1 br.2] at db₂
  have fin : r ^ 2 ≤ r ^ (m - n) := by linarith
  rwa [pow_le_pow_iff_right_of_lt_one₀ br.1 br.2] at fin

theorem result : {a : ℤ | 0 < a ∧ a ^ n + a ^ 2 - 1 ∣ a ^ m + a - 1}.Infinite ↔ m = 5 ∧ n = 3 := by
  refine ⟨proof_body hm hn, fun h ↦ ?_⟩
  rw [h.1, h.2]
  conv =>
    enter [1, 1, a]
    rw [show a ^ 5 + a - 1 = (a ^ 2 - a + 1) * (a ^ 3 + a ^ 2 - 1) by ring]
  simpa using! Set.Ioi_infinite 0

/-- For positive integer inputs, the denominator is strictly positive. -/
lemma denominator_pos {a : ℤ} (ha : 0 < a) (n : ℕ) :
    0 < a ^ n + a ^ 2 - 1 := by
  have hp : 0 < a ^ n := pow_pos ha n
  have ha1 : 1 ≤ a := ha
  nlinarith [sq_nonneg (a - 1)]

/-- Integrality of the rational quotient is equivalent to integer divisibility.
Using rational division avoids the truncated division operation on integers. -/
lemma quotient_integer_iff_dvd {a : ℤ} (ha : 0 < a) (m n : ℕ) :
    (∃ z : ℤ, ((a : ℚ) ^ m + a - 1) / ((a : ℚ) ^ n + a ^ 2 - 1) = z) ↔
      a ^ n + a ^ 2 - 1 ∣ a ^ m + a - 1 := by
  have hdenZ : a ^ n + a ^ 2 - 1 ≠ 0 := ne_of_gt (denominator_pos ha n)
  have hden : (a : ℚ) ^ n + a ^ 2 - 1 ≠ 0 := by exact_mod_cast hdenZ
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have h := (div_eq_iff hden).mp hz
    have h' : (a : ℚ) ^ m + a - 1 = ((a : ℚ) ^ n + a ^ 2 - 1) * z := by
      simpa only [mul_comm] using h
    exact_mod_cast h'
  · rintro ⟨z, hz⟩
    refine ⟨z, (div_eq_iff hden).mpr ?_⟩
    have h' : a ^ m + a - 1 = z * (a ^ n + a ^ 2 - 1) := by
      simpa only [mul_comm] using hz
    exact_mod_cast h'

/-- Divisibility formulation: the unique pair is (5, 3). -/
theorem imo2002_p3_divisibility (m n : ℕ) (hm : 3 ≤ m) (hn : 3 ≤ n) :
    Set.Infinite {a : ℤ | 0 < a ∧ a ^ n + a ^ 2 - 1 ∣ a ^ m + a - 1} ↔
      m = 5 ∧ n = 3 :=
  result hm hn
