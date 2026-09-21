theorem candidate (A B C P : Point) (hP : StrictlyInside P A B C) :
    angleLE30 P A B ∨ angleLE30 P B C ∨ angleLE30 P C A :=
