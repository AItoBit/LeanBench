namespace Imo1993P2

/-- Direction of the tangent at `c` to the circle through `p`, `c`, `d`, given by the
tangent–chord angle: the angle from the chord `cd` to the tangent equals the inscribed angle
`∠dpc`. -/
noncomputable def tangentDir (p c d : ℂ) : ℂ := (d - c) * (d - p) / (c - p)
