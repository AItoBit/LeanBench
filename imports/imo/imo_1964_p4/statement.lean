open Imo1964P4 in
/--
Each pair from $17$ people exchange letters on one of three topics. Prove that there are at least
$3$ people who write to each other on the same topic. [In other words, if we color the edges of the
complete graph $K_{17}$ with three colors, then we can find a triangle all the same color.]
-/
theorem candidate
    -- a topic corresponding to each unordered pair of distinct people
    (topic : Sym2 (Fin 17) → Fin 3) :
    ∃ (s : Finset (Fin 17)) (t : Fin 3),
      3 ≤ s.card ∧ ∀ x ∈ s, ∀ y ∈ s, ∀ (_h : x ≠ y), topic s(x, y) = t :=
