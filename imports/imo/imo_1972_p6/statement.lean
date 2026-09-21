/-- **IMO 1972, Problem 6.**  Given four distinct parallel planes — all orthogonal to a common
nonzero vector `n`, cutting out the pairwise distinct levels `c 0, c 1, c 2, c 3` — there is a
regular tetrahedron with one vertex on each plane: four points `P i` with `P i` on the `i`-th
plane, whose pairwise distances are all equal to a single positive number `s`. -/
theorem candidate (n : E3) (hn : n ≠ 0) (c : Fin 4 → ℝ) (hc : Function.Injective c) :
    ∃ (P : Fin 4 → E3) (s : ℝ), 0 < s ∧ (∀ i, ⟪P i, n⟫_ℝ = c i) ∧
      ∀ i j, i ≠ j → dist (P i) (P j) = s :=
