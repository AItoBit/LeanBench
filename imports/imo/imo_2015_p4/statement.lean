/--
A compact wrapper matching the final logic of Solution 2.
-/
theorem candidate
    (A O F G X : Point)
    (hFG :
      F ≠ G)
    (hAFAG :
      distSq A F = distSq A G)
    (hOFOG :
      distSq O F = distSq O G)
    (hXFXG :
      distSq X F = distSq X G) :
    Collinear A O X :=
