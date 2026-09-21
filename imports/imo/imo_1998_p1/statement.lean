/-- IMO 1998, Problem 1, in coordinates along the perpendicular diagonals. -/
theorem candidate
    (a b c d x y : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hnotparallel : a*d - b*c ≠ 0)
    (hinside : Inside a b c d x y)
    (hAB : sqDist (a,0) (x,y) = sqDist (0,b) (x,y))
    (hCD : sqDist (-c,0) (x,y) = sqDist (0,-d) (x,y)) :
    Cyclic (a,0) (0,b) (-c,0) (0,-d) ↔
      area (a,0) (0,b) (x,y) = area (-c,0) (0,-d) (x,y) :=
