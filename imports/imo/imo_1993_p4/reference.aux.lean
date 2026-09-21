/-- 
The core algebraic identity behind the geometric lemma:
If Y is a convex combination of D and E, the squared distance from the origin
to Y satisfies a specific exact identity based on Apollonius's theorem. 
-/
theorem convex_distance_sq_identity (d1 d2 e1 e2 t : ℝ) :
    normSq (t * d1 + (1 - t) * e1) (t * d2 + (1 - t) * e2) =
    t * normSq d1 d2 + (1 - t) * normSq e1 e2 - t * (1 - t) * normSq (d1 - e1) (d2 - e2) := by
  dsimp [normSq]
  ring
