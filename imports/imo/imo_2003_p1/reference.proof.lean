by
  obtain ⟨T, hTS, hTcard, hgood⟩ := imo2003_p1_finset A hAS hA
  let e : Fin 100 ≃ {t // t ∈ T} := (Finset.equivFinOfCardEq hTcard).symm
  refine ⟨fun i => (e i).val, ?_, ?_, ?_⟩
  · intro i j hij
    exact e.injective (Subtype.ext hij)
  · intro i
    exact hTS (e i).property
  · intro i j hij
    apply hgood (e i).val (e i).property (e j).val (e j).property
    intro heq
    exact hij (e.injective (Subtype.ext heq))
