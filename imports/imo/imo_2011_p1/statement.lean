/--
Both families appearing in the IMO answer attain the maximum.
-/
theorem candidate
    (p : ℕ)
    (hp : 0 < p) :
    goodPairCount
        p (5 * p) (7 * p) (11 * p) = 4
    ∧
    goodPairCount
        p (11 * p) (19 * p) (29 * p) = 4 :=
