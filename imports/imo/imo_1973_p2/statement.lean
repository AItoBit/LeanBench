/-- **IMO 1973, Problem 2.**  Such a set exists. -/
theorem candidate :
    ∃ M : Finset Pt,
      (∃ A ∈ M, ∃ B ∈ M, ∃ C ∈ M, ∃ D ∈ M,
          det (sub B A) (sub C A) (sub D A) ≠ 0) ∧
      (∀ A ∈ M, ∀ B ∈ M, A ≠ B → ∃ C ∈ M, ∃ D ∈ M, C ≠ D ∧
          cross (sub B A) (sub D C) = (0, 0, 0) ∧
          cross (sub C A) (sub B A) ≠ (0, 0, 0)) :=
