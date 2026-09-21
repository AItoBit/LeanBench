open MeasureTheory Set Module Pointwise

/-- Ambient 3-dimensional Euclidean space. -/

abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- **IMO 1971, Problem 2.**  Given a solid convex polyhedron `K` with vertices
`A 0, …, A 8` and the nine translates `P i` of `K` carrying `A 0` to `A i`, two
of the `P i` share an interior point. -/

theorem candidate
    (A : Fin 9 → E3)
    (K : Set E3)
    (hKdef : K = convexHull ℝ (Set.range A))
    (hsolid : (interior K).Nonempty)
    (P : Fin 9 → Set E3)
    (hPdef : ∀ i, P i = (fun x => x + (A i - A 0)) '' K) :
    ∃ i j, i ≠ j ∧ (interior (P i) ∩ interior (P j)).Nonempty :=
