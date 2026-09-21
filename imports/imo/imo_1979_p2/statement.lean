/-- **IMO 1979, Problem 2.** All ten sides of the two pentagons are coloured with the
same colour. -/
theorem candidate
    (hA : ∀ i j : Fin 5, ¬ (a i = c i j ∧ a i = c (i + 1) j))
    (hB : ∀ i j : Fin 5, ¬ (b j = c i j ∧ b j = c i (j + 1))) :
    ∃ col : Bool, (∀ i, a i = col) ∧ (∀ j, b j = col) :=
