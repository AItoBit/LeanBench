/-- **Part (b).** The tangents at `c` to the two circumcircles are perpendicular. -/
theorem candidate (a b c d : ℂ)
    (hD : (a - c) * (b - d) = -Complex.I * ((a - d) * (b - c)))
    (hac : c - a ≠ 0) (hbc : c - b ≠ 0) :
    (tangentDir a c d * (starRingEnd ℂ) (tangentDir b c d)).re = 0 :=
