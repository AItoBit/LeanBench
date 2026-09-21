by

  refine
    ⟨by norm_num,
     h3,
     ?_⟩

  intro m hmpos hmlt

  have hmCases :
      m = 1 ∨ m = 2 := by
    omega

  rcases hmCases with hm1 | hm2

  · subst m
    exact h1

  · subst m
    exact h2

/-!
============================================================
9. Explicit numerical conclusion
============================================================
-/
