/-- **IMO 1981, Problem 5.**  Three congruent circles with common radius `r` and centres
`OA`, `OB`, `OC` lie inside the triangle `A B C`; the one centred at `OA` touches the sides
`AB` and `AC`, the one centred at `OB` touches `AB` and `BC`, and the one centred at `OC`
touches `AC` and `BC`.  If they all pass through a point `O` (and they are not all the same
circle), then the incenter, the circumcenter `X` and `O` are collinear. -/
theorem candidate (A B C OA OB OC O X : Pt) (r : ℝ)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Pt))
    (hOAmem : OA ∈ convexHull ℝ ({A, B, C} : Set Pt))
    (hOBmem : OB ∈ convexHull ℝ ({A, B, C} : Set Pt))
    (hOCmem : OC ∈ convexHull ℝ ({A, B, C} : Set Pt))
    (hOA1 : TangentToLine OA r A B) (hOA2 : TangentToLine OA r A C)
    (hOB1 : TangentToLine OB r A B) (hOB2 : TangentToLine OB r B C)
    (hOC1 : TangentToLine OC r A C) (hOC2 : TangentToLine OC r B C)
    (hne : OA ≠ OB)
    (hOOA : dist O OA = r) (hOOB : dist O OB = r) (hOOC : dist O OC = r)
    (hXB : dist X A = dist X B) (hXC : dist X A = dist X C) :
    Collinear ℝ ({incenter A B C, X, O} : Set Pt) :=
