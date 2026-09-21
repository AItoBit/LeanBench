/-- **IMO 1982, Problem 6 — the estimate.**  Suppose the vertices `A j` and
`A k` of the path both lie within `1/2` of one boundary point `Z`, that an
intermediate vertex `A m` lies within `1/2` of a point `B` at distance at least
`100` from `Z` (a far vertex of the square).  Then `A j` and `A k` are at
distance at most `1`, while the part of the path between them has length at
least `198`. -/
theorem candidate (A : ℕ → P) {j m k : ℕ} (hjm : j ≤ m) (hmk : m ≤ k)
    (Z B : P) (hXZ : dist (A j) Z ≤ 1 / 2) (hYZ : dist (A k) Z ≤ 1 / 2)
    (hB : dist (A m) B ≤ 1 / 2) (hZB : 100 ≤ dist Z B) :
    dist (A j) (A k) ≤ 1 ∧ 198 ≤ plen A j k :=
