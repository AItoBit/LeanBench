/-- **IMO 1972, Problem 1.** -/
theorem candidate (S : Finset ℕ) (hcard : S.card = 10)
    (hS : ∀ n ∈ S, 10 ≤ n ∧ n ≤ 99) :
    ∃ A B : Finset ℕ, A ⊆ S ∧ B ⊆ S ∧ A.Nonempty ∧ B.Nonempty ∧
      Disjoint A B ∧ ∑ x ∈ A, x = ∑ x ∈ B, x :=
