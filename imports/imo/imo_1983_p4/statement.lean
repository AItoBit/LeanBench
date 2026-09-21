/-- **IMO 1983, Problem 4.**  For every partition of the union `E` of the three sides of an
equilateral triangle `ABC` into two disjoint subsets `S` and `T`, at least one of `S`, `T`
contains the three vertices of a right-angled triangle.  (The disjointness hypothesis is not
needed for the conclusion.) -/
theorem candidate (A B C : Pt) (hABBC : dist A B = dist B C) (hBCCA : dist B C = dist C A)
    (hAB : A ≠ B) (S T : Set Pt) (hunion : S ∪ T = sides A B C) (hdisj : Disjoint S T) :
    HasRightTriangle S ∨ HasRightTriangle T :=
