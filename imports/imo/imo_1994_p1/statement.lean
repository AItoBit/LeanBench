open scoped Nat

/-- IMO 1994, Problem 1. -/

theorem candidate (m n : ℕ) (a : ℕ → ℕ) (h₀ : 0 < m ∧ 0 < n)
    (h₁ : Set.MapsTo a (Set.Icc 1 m) (Set.Icc 1 n))
    (h₂ : Set.InjOn a (Set.Icc 1 m))
    (h₃ :
      ∀ i ∈ Finset.Icc 1 m, ∀ j ∈ Finset.Icc 1 m,
        i ≤ j ∧ a i + a j ≤ n → ∃ k ∈ Finset.Icc 1 m, a i + a j = a k) :
    (n + 1 : ℚ) / 2 ≤ (∑ i ∈ Finset.Icc 1 m, a i : ℚ) / m :=
