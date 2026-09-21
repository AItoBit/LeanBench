/-- **IMO 1966, Problem 3.**  Let `A B C D` be the vertices of a regular tetrahedron in
Euclidean 3-space (all six edges have the same positive length `s`), and let `O` be the
center of its circumscribed sphere (the point equidistant from the four vertices).
Then for every point `P ≠ O`, the sum of the distances from `O` to the vertices is strictly
less than the sum of the distances from `P` to the vertices. -/
theorem candidate (A B C D O P : E) (s : ℝ) (hs : 0 < s)
    (hAB : dist A B = s) (hAC : dist A C = s) (hAD : dist A D = s)
    (hBC : dist B C = s) (hBD : dist B D = s) (hCD : dist C D = s)
    (hOA : dist O A = dist O B) (hOB : dist O B = dist O C) (hOC : dist O C = dist O D)
    (hPO : P ≠ O) :
    dist O A + dist O B + dist O C + dist O D
      < dist P A + dist P B + dist P C + dist P D :=
