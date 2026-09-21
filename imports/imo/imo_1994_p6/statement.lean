/-- IMO 1994, Problem 6. -/
theorem candidate (is_prod_of_k_distinct_elements : ℕ → ℕ → Set ℕ → Prop)
    (h₀ :
      is_prod_of_k_distinct_elements = fun n k S =>
        ∃ Sₙ : Finset ℕ, ↑Sₙ ⊆ S ∧ Finset.card Sₙ = k ∧ ∏ x ∈ Sₙ, x = n) :
    ∃ A : Set ℕ,
      (∀ a ∈ A, 0 < a) ∧
        ∀ S : Set ℕ,
          (S.Infinite ∧ ∀ s ∈ S, Nat.Prime s) →
            ∃ m ∈ A, ∃ n ∉ A, ∃ k ≥ 2, 0 < m ∧ 0 < n ∧
              is_prod_of_k_distinct_elements m k S ∧
                is_prod_of_k_distinct_elements n k S :=
