/-- **IMO 2005 P1.** The three main diagonals of the hexagon all pass through the centroid
`(0, h/3)` of the triangle, hence are concurrent. -/
theorem candidate (p q r t h : ℝ) (hh : h ^ 2 = 3 / 4) (hh0 : 0 < h)
    (hsig : 0 < 1 - t)
    -- the three corner sides of the hexagon have length `t`
    (hA : (1 - t - p) ^ 2 + q ^ 2 - (1 - t - p) * q = t ^ 2)
    (hB : (1 - t - q) ^ 2 + r ^ 2 - (1 - t - q) * r = t ^ 2)
    (hC : (1 - t - r) ^ 2 + p ^ 2 - (1 - t - r) * p = t ^ 2) :
    -- `A₁`, `O`, `B₂` are collinear
    cross (-1 / 2 + p) 0 0 (h / 3) (1 / 2 - (q + t) / 2) ((q + t) * h) = 0 ∧
    -- `B₁`, `O`, `C₂` are collinear
    cross (1 / 2 - q / 2) (q * h) 0 (h / 3) (-(r + t) / 2) (h - (r + t) * h) = 0 ∧
    -- `C₁`, `O`, `A₂` are collinear
    cross (-r / 2) (h - r * h) 0 (h / 3) (-1 / 2 + (p + t)) 0 = 0 :=
