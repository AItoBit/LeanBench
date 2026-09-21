by
  by_cases h1 : n = 1
  · subst n
    constructor
    · norm_num [spread, energy]
    · constructor
      · intro _
        refine ⟨x 0, 0, ?_⟩
        intro i hi
        have hi0 : i = 0 := by omega
        subst i
        simp
      · intro _
        norm_num [spread, energy]
  · exact main_of_two_le n (by omega) x hx
