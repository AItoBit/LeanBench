theorem candidate
    {Step : Board → Board → Prop}
    {measure signature : Board → ℕ}
    (F :
      SourceFacts
        Step
        measure
        signature)
    (initial : Board)
    (hinit :
      ∀ i : Fin 2026,
        1 < initial i) :

    (¬ InfiniteRunFrom Step initial)
    ∧
    (
      ∀ final : Board,
        Reach Step initial final →
        Stopped final →
        ∃ M : ℕ,
          ExactlyOneLarge final M
    )
    ∧
    (
      ∀ final₁ final₂ : Board,
        ∀ M₁ M₂ : ℕ,
          Reach Step initial final₁ →
          Reach Step initial final₂ →
          ExactlyOneLarge final₁ M₁ →
          ExactlyOneLarge final₂ M₂ →
          M₁ = M₂
    ) :=
