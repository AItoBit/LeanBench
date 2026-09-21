by
  obtain ⟨hpq, hqr⟩ := equal_sides_symmetric hsig hA hB hC
  subst hpq
  subst hqr
  refine ⟨?_, ?_, ?_⟩
  · simp only [cross]; linear_combination (-h / 3) * hA
  · simp only [cross]; linear_combination (-h / 3) * hA
  · simp only [cross]; linear_combination (-h / 3) * hA
