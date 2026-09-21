by
  subst hS
  refine ⟨fun hA ↦ ?_, fun hA ↦ ?_, fun hA ↦ ?_⟩ <;> subst hA
  · exact candidate.parts.a
  · exact candidate.parts.b
  · exact candidate.parts.c
