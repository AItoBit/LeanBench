/-- In each round the three players together receive `p + q + r` counters. -/
theorem round_sum {n p q r : ℕ} {a b c : ℕ → ℕ}
    (hdeal : ∀ i < n, ({a i, b i, c i} : Multiset ℕ) = {p, q, r}) :
    ∀ i < n, a i + b i + c i = p + q + r := by
  intro i hi
  have h := congrArg Multiset.sum (hdeal i hi)
  simpa [add_assoc] using h

/-- In each round every player receives one of the three amounts `p`, `q`, `r`. -/
theorem mem_cards {n p q r : ℕ} {a b c : ℕ → ℕ}
    (hdeal : ∀ i < n, ({a i, b i, c i} : Multiset ℕ) = {p, q, r}) :
    ∀ i < n, (a i = p ∨ a i = q ∨ a i = r) ∧ (b i = p ∨ b i = q ∨ b i = r) ∧
      (c i = p ∨ c i = q ∨ c i = r) := by
  intro i hi
  have ha : a i ∈ ({p, q, r} : Multiset ℕ) := by rw [← hdeal i hi]; simp
  have hb : b i ∈ ({p, q, r} : Multiset ℕ) := by rw [← hdeal i hi]; simp
  have hc : c i ∈ ({p, q, r} : Multiset ℕ) := by rw [← hdeal i hi]; simp
  refine ⟨by simpa using ha, by simpa using hb, by simpa using hc⟩

/-- There were exactly three rounds, and `p + q + r = 13`. -/
theorem three_rounds {n p q r : ℕ} {a b c : ℕ → ℕ}
    (hn : 2 ≤ n) (hp : 0 < p) (hpq : p < q) (hqr : q < r)
    (hdeal : ∀ i < n, ({a i, b i, c i} : Multiset ℕ) = {p, q, r})
    (hA : ∑ i ∈ Finset.range n, a i = 20)
    (hB : ∑ i ∈ Finset.range n, b i = 10)
    (hC : ∑ i ∈ Finset.range n, c i = 9) :
    n = 3 ∧ p + q + r = 13 := by
  have key : n * (p + q + r) = 39 := by
    have h : ∑ i ∈ Finset.range n, (a i + b i + c i) = n * (p + q + r) := by
      rw [Finset.sum_congr rfl (fun i hi => round_sum hdeal i (Finset.mem_range.mp hi))]
      simp [Finset.sum_const]
    rw [← h]
    simp only [Finset.sum_add_distrib, hA, hB, hC]
  have hs : 6 ≤ p + q + r := by omega
  have hn6 : n ≤ 6 := by nlinarith
  interval_cases n <;> omega
