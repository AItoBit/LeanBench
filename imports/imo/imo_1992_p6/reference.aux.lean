/-- A sum whose terms all lie in `{0, 3, 8}` is a non-negative combination of `3` and `8`. -/
theorem sum_semigroup (s : Finset ℕ) (g : ℕ → ℕ) :
    (∀ i ∈ s, g i = 0 ∨ g i = 3 ∨ g i = 8) → ∃ a b : ℕ, ∑ i ∈ s, g i = 3 * a + 8 * b := by
  classical
  refine Finset.induction_on s ?_ ?_
  · intro _
    exact ⟨0, 0, by simp⟩
  · intro x t hx ih hall
    obtain ⟨a, b, hab⟩ := ih fun i hi => hall i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert hx]
    rcases hall x (Finset.mem_insert_self x t) with h0 | h3 | h8
    · exact ⟨a, b, by rw [h0, hab]; ring⟩
    · exact ⟨a + 1, b, by rw [h3, hab]; ring⟩
    · exact ⟨a, b + 1, by rw [h8, hab]; ring⟩

/-! ### `n²` is not a sum of `n² - 13` positive squares -/

theorem not_rep_thirteen (n k : ℕ) (hk : k + 13 = n ^ 2) : ¬ Rep n k := by
  rintro ⟨f, hpos, hsum⟩
  -- rewrite the sum of squares as `Σ (aᵢ² - 1) + k`
  have hstep : ∑ i ∈ Finset.range k, (f i) ^ 2
      = (∑ i ∈ Finset.range k, ((f i) ^ 2 - 1)) + k := by
    have hcongr : ∑ i ∈ Finset.range k, (f i) ^ 2
        = ∑ i ∈ Finset.range k, (((f i) ^ 2 - 1) + 1) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have h1 := hpos i (Finset.mem_range.1 hi)
      have h2 : 1 ≤ (f i) ^ 2 := Nat.one_le_pow 2 (f i) h1
      omega
    rw [hcongr, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  have hG : ∑ i ∈ Finset.range k, ((f i) ^ 2 - 1) = 13 := by omega
  -- every term is at most 13, hence lies in `{0, 3, 8}`
  have hmem : ∀ i ∈ Finset.range k, ((f i) ^ 2 - 1) = 0 ∨ ((f i) ^ 2 - 1) = 3
      ∨ ((f i) ^ 2 - 1) = 8 := by
    intro i hi
    have hle : (f i) ^ 2 - 1 ≤ 13 := by
      have := Finset.single_le_sum (f := fun j => (f j) ^ 2 - 1) (fun j _ => Nat.zero_le _) hi
      omega
    have h1 := hpos i (Finset.mem_range.1 hi)
    have hf3 : f i ≤ 3 := by
      by_contra hcon
      rw [Nat.not_le] at hcon
      have : 4 ^ 2 ≤ (f i) ^ 2 := Nat.pow_le_pow_left hcon 2
      omega
    interval_cases h : f i <;> simp_all
  obtain ⟨a, b, hab⟩ := sum_semigroup _ _ hmem
  omega

/-! ### Part (a) -/

theorem part_a (n : ℕ) (hn : 4 ≤ n) (m : ℕ) (hm : Good n m) : m ≤ n ^ 2 - 14 := by
  by_contra hcon
  rw [Nat.not_le] at hcon
  have hn2 : 16 ≤ n ^ 2 := by nlinarith
  exact not_rep_thirteen n (n ^ 2 - 13) (by omega) (hm _ (by omega) (by omega))

/-! ### The construction supplying most `k` -/
