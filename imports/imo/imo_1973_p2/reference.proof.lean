by
  refine ⟨M, ?_, ?_⟩
  · exact ⟨(0, 0, 0), by decide, (1, 0, 0), by decide, (0, 1, 0), by decide,
      (0, 0, 1), by decide, by decide⟩
  · intro A hA B hB hAB
    obtain ⟨h1, h2, h3, h4, h5⟩ := wit_spec A hA B hB hAB
    exact ⟨(wit A B).1, h1, (wit A B).2, h2, h3, h4, h5⟩
