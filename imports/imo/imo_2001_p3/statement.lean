/-- IMO 2001, Problem 3, with the hypotheses and conclusion stated explicitly.
The natural numbers label the competition problems. -/
theorem candidate (G B : Fin 21 → Finset ℕ)
    (hG : ∀ i, (G i).card ≤ 6)
    (hB : ∀ j, (B j).card ≤ 6)
    (hcommon : ∀ i j, ∃ p, p ∈ G i ∧ p ∈ B j) :
    ∃ p : ℕ,
      3 ≤ (Finset.univ.filter (fun i : Fin 21 => p ∈ G i)).card ∧
      3 ≤ (Finset.univ.filter (fun j : Fin 21 => p ∈ B j)).card :=
