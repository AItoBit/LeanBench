/-- **IMO 1999, Problem 1.**  A finite set `S` of at least three points of the plane has the
property that for any two distinct points `A, B ∈ S` the perpendicular bisector of `AB` is an
axis of symmetry of `S` if and only if `S` is the set of vertices of a regular `n`-gon, where
`n = |S|`: that is, `S = {c + w * u | u ^ n = 1}` for some centre `c` and some `w ≠ 0`. -/
theorem candidate (S : Finset ℂ) (hS : 3 ≤ S.card) :
    (∀ A ∈ S, ∀ B ∈ S, A ≠ B → ∀ z ∈ S, reflBis A B z ∈ S) ↔
      ∃ c w : ℂ, w ≠ 0 ∧ (S : Set ℂ) = {z | ∃ u : ℂ, u ^ S.card = 1 ∧ z = c + w * u} :=
