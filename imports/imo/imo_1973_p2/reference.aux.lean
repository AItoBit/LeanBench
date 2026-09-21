/-- The whole verification, as a finite check over the `27 × 27` pairs. -/
private lemma wit_spec : ∀ A ∈ M, ∀ B ∈ M, A ≠ B →
    (wit A B).1 ∈ M ∧ (wit A B).2 ∈ M ∧ (wit A B).1 ≠ (wit A B).2 ∧
      cross (sub B A) (sub (wit A B).2 (wit A B).1) = (0, 0, 0) ∧
      cross (sub (wit A B).1 A) (sub B A) ≠ (0, 0, 0) := by
  decide
