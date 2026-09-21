/-- **IMO 1978, Problem 5.** Let `f` be an injective function from `{1, 2, 3, …}` into itself.
Then for every `n`, `∑_{k=1}^n f(k) / k² ≥ ∑_{k=1}^n 1/k`. -/
theorem candidate (f : ℕ → ℕ) (hinj : Set.InjOn f {k : ℕ | 1 ≤ k})
    (hpos : ∀ k : ℕ, 1 ≤ k → 1 ≤ f k) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / (k : ℝ) ≤ ∑ k ∈ Finset.Icc 1 n, (f k : ℝ) / (k : ℝ) ^ 2 :=
