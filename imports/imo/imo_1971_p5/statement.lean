open scoped Classical in
/-- **IMO 1971, Problem 5.**  For every `m` there is a finite set of points of
the plane in which every point has exactly `m` points at unit distance. -/
theorem candidate (m : ℕ) :
    ∃ S : Finset ℂ, ∀ A ∈ S, (S.filter (fun B => dist A B = 1)).card = m :=
