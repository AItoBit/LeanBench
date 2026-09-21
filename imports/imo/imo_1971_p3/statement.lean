/-- **IMO 1971, Problem 3.**  The set of integers of the form `2 ^ k - 3`
(`k ≥ 2`) contains an infinite subset whose members are pairwise coprime. -/
theorem candidate :
    ∃ S : Set ℕ,
      S.Infinite ∧
      S ⊆ {n : ℕ | ∃ k : ℕ, 2 ≤ k ∧ n = 2 ^ k - 3} ∧
      ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Nat.Coprime x y :=
