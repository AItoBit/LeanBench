by
  refine ⟨fun i => (((i : ℕ) : ℝ), ((i : ℕ) : ℝ) ^ 2), ?_, ?_, ?_⟩
  · intro i j h
    simp only [Prod.mk.injEq] at h
    exact Fin.ext (by exact_mod_cast h.1)
  · intro i j hij
    have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    exact irrational_eDist hne
  · intro i j k hij hjk hik
    have h1 : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    have h2 : (j : ℕ) ≠ (k : ℕ) := fun h => hjk (Fin.ext h)
    have h3 : (i : ℕ) ≠ (k : ℕ) := fun h => hik (Fin.ext h)
    exact triArea_facts h1 h2 h3
