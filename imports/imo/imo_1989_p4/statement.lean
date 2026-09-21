/-- Extremal configuration: circles of radii `a` and `b` tangent to the line `y = 0` from above
and externally tangent to each other; a circle of radius `h` tangent to the line and to both,
horizontally between them. Then equality holds, so the bound of `imo1989_p4_core` is sharp. -/
theorem candidate {a b h p q r : ℝ} (ha : 0 < a) (hb : 0 < b) (hh : 0 < h)
    (hAB : Real.sqrt ((p - q) ^ 2 + (a - b) ^ 2) = a + b)
    (hAP : Real.sqrt ((p - r) ^ 2 + (a - h) ^ 2) = a + h)
    (hBP : Real.sqrt ((r - q) ^ 2 + (h - b) ^ 2) = h + b)
    (hbet : 0 ≤ (p - r) * (r - q)) :
    1 / Real.sqrt h = 1 / Real.sqrt a + 1 / Real.sqrt b :=
