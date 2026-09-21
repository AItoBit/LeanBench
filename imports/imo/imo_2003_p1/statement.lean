/-- IMO 2003, Problem 1, with an explicit indexed family of 100 distinct shifts. -/
theorem candidate (A : Finset ℤ) (hAS : A ⊆ Icc 1 1000000) (hA : A.card = 101) :
    ∃ x : Fin 100 → ℤ,
      Function.Injective x ∧
      (∀ i, x i ∈ Icc 1 1000000) ∧
      ∀ i j, i ≠ j →
        Disjoint (A.image (fun a => a + x i)) (A.image (fun a => a + x j)) :=
