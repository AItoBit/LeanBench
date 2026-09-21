by
  classical
  set k : ℕ := n ^ 2 - (3 * a + 8 * b) with hk
  have hab : a + b ≤ k := by omega
  refine ⟨fun i => if i < a then 2 else if i < a + b then 3 else 1, ?_, ?_⟩
  · intro i _
    dsimp only
    split_ifs <;> omega
  · have hsplit : ∑ i ∈ Finset.range k,
        ((if i < a then 2 else if i < a + b then 3 else 1) : ℕ) ^ 2
        = (∑ i ∈ Finset.Ico 0 a, ((if i < a then 2 else if i < a + b then 3 else 1) : ℕ) ^ 2)
          + (∑ i ∈ Finset.Ico a (a + b), ((if i < a then 2 else if i < a + b then 3 else 1) : ℕ) ^ 2)
          + (∑ i ∈ Finset.Ico (a + b) k,
              ((if i < a then 2 else if i < a + b then 3 else 1) : ℕ) ^ 2) := by
      rw [Finset.range_eq_Ico]
      rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le a) (le_trans (Nat.le_add_right a b) hab),
        ← Finset.sum_Ico_consecutive _ (Nat.le_add_right a b) hab]
      ring
    have h1 : ∑ i ∈ Finset.Ico 0 a,
        ((if i < a then 2 else if i < a + b then 3 else 1) : ℕ) ^ 2 = 4 * a := by
      have hc : ∀ i ∈ Finset.Ico 0 a,
          ((if i < a then 2 else if i < a + b then 3 else 1) : ℕ) ^ 2 = 4 := by
        intro i hi
        rw [Finset.mem_Ico] at hi
        simp [hi.2]
      calc ∑ i ∈ Finset.Ico 0 a, ((if i < a then 2 else if i < a + b then 3 else 1) : ℕ) ^ 2
          = ∑ _i ∈ Finset.Ico 0 a, (4 : ℕ) := Finset.sum_congr rfl hc
        _ = 4 * a := by rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]; omega
    have h2 : ∑ i ∈ Finset.Ico a (a + b),
        ((if i < a then 2 else if i < a + b then 3 else 1) : ℕ) ^ 2 = 9 * b := by
      have hc : ∀ i ∈ Finset.Ico a (a + b),
          ((if i < a then 2 else if i < a + b then 3 else 1) : ℕ) ^ 2 = 9 := by
        intro i hi
        rw [Finset.mem_Ico] at hi
        have hia : ¬ i < a := by omega
        simp [hia, hi.2]
      calc ∑ i ∈ Finset.Ico a (a + b),
            ((if i < a then 2 else if i < a + b then 3 else 1) : ℕ) ^ 2
          = ∑ _i ∈ Finset.Ico a (a + b), (9 : ℕ) := Finset.sum_congr rfl hc
        _ = 9 * b := by rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]; omega
    have h3 : ∑ i ∈ Finset.Ico (a + b) k,
        ((if i < a then 2 else if i < a + b then 3 else 1) : ℕ) ^ 2 = k - (a + b) := by
      have hc : ∀ i ∈ Finset.Ico (a + b) k,
          ((if i < a then 2 else if i < a + b then 3 else 1) : ℕ) ^ 2 = 1 := by
        intro i hi
        rw [Finset.mem_Ico] at hi
        have hia : ¬ i < a := by omega
        have hib : ¬ i < a + b := by omega
        simp [hia, hib]
      calc ∑ i ∈ Finset.Ico (a + b) k,
            ((if i < a then 2 else if i < a + b then 3 else 1) : ℕ) ^ 2
          = ∑ _i ∈ Finset.Ico (a + b) k, (1 : ℕ) := Finset.sum_congr rfl hc
        _ = k - (a + b) := by rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]; omega
    rw [hsplit, h1, h2, h3]
    omega

/-!
### Status of parts (b) and (c)

Both remaining parts need the *positive* direction: that `n²` really is a sum of `k` positive
squares for every `k ≤ n² - 14`.

`candidate` handles every `k` for which `n² - k` can be written as `3a + 8b` with
`4a + 9b ≤ n²`. Since `13` is the Frobenius number of `⟨3, 8⟩`, each `Δ = n² - k ≥ 14` is
`3a + 8b` for some `a, b`; the constraint `4a + 9b ≤ n²`, i.e. `Δ + a + b ≤ n²`, holds once
`Δ ≲ (8/9) n²`, that is for all but the smallest values of `k`.

What is missing is exactly the small-`k` range, where `n²` must be a sum of very few positive
squares:

* `k = 2` needs `n²` to be a sum of two positive squares, so `n` needs a prime factor `≡ 1 mod 4`;
* `k = 3` needs `n²` to be a sum of three positive squares. The AoPS argument invokes Legendre's
  **three-square theorem**, which Mathlib does not have. (Mathlib has Lagrange's four-square
  theorem, `Nat.sum_four_squares`, but no three-square theorem.)

For part (b) with `n = 13` the small range is finite — the `k ≤ 18` cases — so it can be closed
by exhibiting eighteen explicit representations of `169`. For part (c) the small range must be
handled uniformly in `n`; picking `n` in a family such as `n = 15m` gives `k = 2` and `k = 3`
directly, via `(15m)² = (9m)² + (12m)²` and `(15m)² = (10m)² + (10m)² + (5m)²`, avoiding the
three-square theorem, but the intermediate `k` still need a chain of splitting steps.
-/
