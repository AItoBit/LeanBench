/-- `(∑ tᵢ)(∑ 1/tᵢ) ≥ |s|²` for positive `tᵢ`. -/
theorem card_sq_le {ι : Type*} [DecidableEq ι] (t : ι → ℝ) (s : Finset ι) :
    (∀ i ∈ s, 0 < t i) → ((s.card : ℝ)) ^ 2 ≤ (∑ i ∈ s, t i) * (∑ i ∈ s, 1 / t i) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | @insert a s ha ih =>
      intro hpos
      have hta : 0 < t a := hpos a (Finset.mem_insert_self a s)
      have hps : ∀ i ∈ s, 0 < t i := fun i hi => hpos i (Finset.mem_insert_of_mem hi)
      have hih := ih hps
      have hR : 0 ≤ ∑ i ∈ s, t i := Finset.sum_nonneg fun i hi => (hps i hi).le
      have hU : 0 ≤ ∑ i ∈ s, 1 / t i :=
        Finset.sum_nonneg fun i hi => (one_div_pos.2 (hps i hi)).le
      have hcard : (0 : ℝ) ≤ (s.card : ℝ) := Nat.cast_nonneg _
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
      push_cast
      have hprod : (t a * (∑ i ∈ s, 1 / t i)) * ((∑ i ∈ s, t i) / t a)
          = (∑ i ∈ s, t i) * (∑ i ∈ s, 1 / t i) := by
        field_simp
        ring
      have hnn : 0 ≤ t a * (∑ i ∈ s, 1 / t i) + (∑ i ∈ s, t i) / t a := by positivity
      have hge : 2 * (s.card : ℝ)
          ≤ t a * (∑ i ∈ s, 1 / t i) + (∑ i ∈ s, t i) / t a := by
        nlinarith [sq_nonneg (t a * (∑ i ∈ s, 1 / t i) - (∑ i ∈ s, t i) / t a),
          hih, hnn, hprod, hcard]
      have hexp : (t a + ∑ i ∈ s, t i) * (1 / t a + ∑ i ∈ s, 1 / t i)
          = 1 + (t a * (∑ i ∈ s, 1 / t i) + (∑ i ∈ s, t i) / t a)
            + (∑ i ∈ s, t i) * (∑ i ∈ s, 1 / t i) := by
        field_simp
        ring
      rw [hexp]
      nlinarith [hge, hih]

/-- The `n = 3` core: if `a + b ≤ c` then `(a+b+c)(1/a+1/b+1/c) ≥ 10`. -/
theorem three_bound {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b ≤ c) :
    10 ≤ (a + b + c) * (1 / a + 1 / b + 1 / c) := by
  have hk : 0 ≤ c - a - b := by linarith
  have e1 : 0 ≤ (9 * c - a - b) * (a - b) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have e2 : 0 ≤ (a + b) ^ 2 * (c - a - b) := mul_nonneg (sq_nonneg _) hk
  have e3 : 0 ≤ (a + b) * (c - a - b) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have hpoly : 0 ≤ (a + b + c) * (a * b + b * c + c * a) - 10 * (a * b * c) := by
    nlinarith [e1, e2, e3]
  have hrw : (a + b + c) * (1 / a + 1 / b + 1 / c) - 10
      = ((a + b + c) * (a * b + b * c + c * a) - 10 * (a * b * c)) / (a * b * c) := by
    field_simp
    ring
  have : 0 ≤ (a + b + c) * (1 / a + 1 / b + 1 / c) - 10 := by
    rw [hrw]
    exact div_nonneg hpoly (by positivity)
  linarith
