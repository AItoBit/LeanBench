/-- 
Formalization of the problem's geometric lemma: 
"If Y lies between D and E, then FY is less than the greater than FD and FE."

Here, F is shifted to the origin (0, 0). D is (d1, d2) and E is (e1, e2).
Y is represented as the convex combination `t * D + (1 - t) * E` for `0 ≤ t ≤ 1`.
The theorem strictly proves that the squared length of Y is at most the maximum 
of the squared lengths of D and E.
-/
theorem candidate (d1 d2 e1 e2 t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    normSq (t * d1 + (1 - t) * e1) (t * d2 + (1 - t) * e2) ≤
    max (normSq d1 d2) (normSq e1 e2) :=
