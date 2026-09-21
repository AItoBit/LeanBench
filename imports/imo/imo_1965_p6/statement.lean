/-- **IMO 1965, Problem 6.** If every pairwise distance in the finite set `S` is at
most `d`, then the number of pairs at distance exactly `d` is at most `S.card`
(stated with the ordered-pair count, hence the factor `2` on both sides). -/
theorem candidate {d : ℝ} (hd : 0 < d) (geom : MiddlePoint d) :
    ∀ S : Finset Plane, (∀ x ∈ S, ∀ y ∈ S, dist x y ≤ d) →
      pairCount S d ≤ 2 * S.card :=
