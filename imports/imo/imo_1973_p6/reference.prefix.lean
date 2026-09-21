namespace Imo1973P6

/-! ### Powers of `q` -/

private lemma pow_le_one_aux {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) : ∀ d : ℕ, q ^ d ≤ 1 := by
  intro d
  induction d with
  | zero => simp
  | succ m ih =>
    rw [pow_succ]
    nlinarith [pow_nonneg h0 m]

private lemma pow_lt_one_aux {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) {d : ℕ} (hd : 0 < d) :
    q ^ d < 1 := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  rw [pow_succ]
  nlinarith [pow_le_one_aux h0 h1.le e, pow_nonneg h0 e]

private lemma qpow_le {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {m m' : ℕ} (h : m ≤ m') :
    q ^ m' ≤ q ^ m := by
  obtain ⟨d, rfl⟩ : ∃ d, m' = m + d := ⟨m' - m, by omega⟩
  rw [pow_add]
  nlinarith [pow_le_one_aux h0 h1 d, pow_nonneg h0 m]

private lemma qpow_lt {q : ℝ} (h0 : 0 < q) (h1 : q < 1) {m m' : ℕ} (h : m < m') :
    q ^ m' < q ^ m := by
  obtain ⟨d, rfl⟩ : ∃ d, m' = m + d := ⟨m' - m, by omega⟩
  rw [pow_add]
  have hd : 0 < d := by omega
  nlinarith [pow_lt_one_aux h0.le h1 hd, pow_pos h0 m]

private lemma geom_id (q : ℝ) : ∀ m : ℕ,
    (1 - q) * ∑ i ∈ Finset.range m, q ^ i = 1 - q ^ m := by
  intro m
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
    ring

private lemma geom_lt {q : ℝ} (h0 : 0 < q) (m : ℕ) :
    (1 - q) * ∑ i ∈ Finset.range m, q ^ i < 1 := by
  rw [geom_id]
  have := pow_pos h0 m
  linarith

/-! ### The construction -/

/-- `dd k j = |k - j|`. -/
private def dd (k j : ℕ) : ℕ := (k - j) + (j - k)

private lemma dd_self (k : ℕ) : dd k k = 0 := by simp [dd]

private lemma dd_succ_le (k j : ℕ) : dd (k + 1) j ≤ dd k j + 1 := by simp only [dd]; omega

private lemma dd_le_succ (k j : ℕ) : dd k j ≤ dd (k + 1) j + 1 := by simp only [dd]; omega

/-- `cₖ = ∑ⱼ q^{|k-j|} aⱼ`. -/
private noncomputable def cc (n : ℕ) (q : ℝ) (a : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, q ^ dd k j * a j

private lemma cc_pos {n : ℕ} {q : ℝ} {a : ℕ → ℝ} (hn : 0 < n) (hq0 : 0 < q)
    (ha : ∀ j, 0 < a j) (k : ℕ) : 0 < cc n q a k := by
  refine Finset.sum_pos (fun j _ => mul_pos (pow_pos hq0 _) (ha j)) ?_
  exact Finset.nonempty_range_iff.mpr (by omega)

private lemma le_cc {n : ℕ} {q : ℝ} {a : ℕ → ℝ} (hq0 : 0 < q) (ha : ∀ j, 0 < a j)
    {k : ℕ} (hk : k < n) : a k ≤ cc n q a k := by
  have h := Finset.single_le_sum
    (f := fun j => q ^ dd k j * a j)
    (fun j _ => le_of_lt (mul_pos (pow_pos hq0 _) (ha j)))
    (Finset.mem_range.mpr hk)
  rw [dd_self, pow_zero, one_mul] at h
  exact h

private lemma cc_lower {n : ℕ} {q : ℝ} {a : ℕ → ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (ha : ∀ j, 0 < a j) {k : ℕ} (hk : k + 1 < n) :
    q * cc n q a k < cc n q a (k + 1) := by
  have hmul : q * cc n q a k = ∑ j ∈ Finset.range n, q ^ (dd k j + 1) * a j := by
    unfold cc
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_succ]
    ring
  rw [hmul]
  unfold cc
  refine Finset.sum_lt_sum (fun j _ => ?_) ⟨k + 1, Finset.mem_range.mpr hk, ?_⟩
  · exact mul_le_mul_of_nonneg_right
      (qpow_le hq0.le hq1.le (dd_succ_le k j)) (ha j).le
  · refine mul_lt_mul_of_pos_right (qpow_lt hq0 hq1 ?_) (ha (k + 1))
    simp only [dd]; omega

private lemma cc_upper {n : ℕ} {q : ℝ} {a : ℕ → ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (ha : ∀ j, 0 < a j) {k : ℕ} (hk : k + 1 < n) :
    q * cc n q a (k + 1) < cc n q a k := by
  have hmul : q * cc n q a (k + 1) = ∑ j ∈ Finset.range n, q ^ (dd (k + 1) j + 1) * a j := by
    unfold cc
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_succ]
    ring
  rw [hmul]
  unfold cc
  refine Finset.sum_lt_sum (fun j _ => ?_) ⟨k, Finset.mem_range.mpr (by omega), ?_⟩
  · exact mul_le_mul_of_nonneg_right
      (qpow_le hq0.le hq1.le (dd_le_succ k j)) (ha j).le
  · refine mul_lt_mul_of_pos_right (qpow_lt hq0 hq1 ?_) (ha k)
    simp only [dd]; omega

/-- The inner sum `∑ₖ q^{|k-j|}` is bounded by `(1+q)/(1-q)`. -/
private lemma inner_bound {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {n j : ℕ} (hj : j < n) :
    ∑ k ∈ Finset.range n, q ^ dd k j < (1 + q) / (1 - q) := by
  have hq' : (0:ℝ) < 1 - q := by linarith
  have hsplit : ∑ k ∈ Finset.range n, q ^ dd k j
      = (∑ k ∈ (Finset.range n).filter (fun k => k ≤ j), q ^ dd k j)
        + (∑ k ∈ (Finset.range n).filter (fun k => ¬ k ≤ j), q ^ dd k j) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hAset : (Finset.range n).filter (fun k => k ≤ j) = Finset.range (j + 1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have hBset : (Finset.range n).filter (fun k => ¬ k ≤ j) = Finset.Ico (j + 1) n := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  have hA : ∑ k ∈ Finset.range (j + 1), q ^ dd k j
      = ∑ i ∈ Finset.range (j + 1), q ^ i := by
    rw [← Finset.sum_range_reflect (fun i => q ^ i) (j + 1)]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [show dd k j = j + 1 - 1 - k from by simp only [dd]; omega]
  have hB : ∑ k ∈ Finset.Ico (j + 1) n, q ^ dd k j
      = q * ∑ i ∈ Finset.range (n - (j + 1)), q ^ i := by
    rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show dd (j + 1 + i) j = i + 1 from by simp only [dd]; omega, pow_succ]
    ring
  have hgA := geom_lt hq0 (j + 1)
  have hgB := geom_lt hq0 (n - (j + 1))
  have hR : (1 + q) / (1 - q) * (1 - q) = 1 + q := by field_simp
  refine lt_of_mul_lt_mul_right ?_ hq'.le
  rw [hR, hsplit, hAset, hBset, hA, hB]
  nlinarith [hgA, hgB, hq0]

/-! ### The theorem -/
