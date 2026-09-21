/-- **IMO 1974, Problem 1.**  Under the conditions of the problem, player `C` received `q`
counters in the first round. -/
theorem candidate {n p q r : ℕ} {a b c : ℕ → ℕ}
    (hn : 2 ≤ n) (hp : 0 < p) (hpq : p < q) (hqr : q < r)
    (hdeal : ∀ i < n, ({a i, b i, c i} : Multiset ℕ) = {p, q, r})
    (hA : ∑ i ∈ Finset.range n, a i = 20)
    (hB : ∑ i ∈ Finset.range n, b i = 10)
    (hC : ∑ i ∈ Finset.range n, c i = 9)
    (hlast : b (n - 1) = r) :
    c 0 = q :=
