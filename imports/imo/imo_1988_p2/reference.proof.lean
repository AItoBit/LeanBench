by
  obtain ⟨h1, h2, h3⟩ := exists_config n
  constructor
  · intro h
    obtain ⟨f, hf⟩ := h (Edge n) (star n) h1 h2 h3
    exact even_of_exists_assignment (star n) h1 h2 h3 f hf
  · intro hn B _ A hA1 hA2 hA3
    exact exists_assignment_of_even A hA1 hA2 hA3 hn
