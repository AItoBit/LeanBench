/--
Suppose the coordinate computation for the three reflected lines has
produced:

* `P`, a common point of the original unit circle and the new circle;
* a nonzero real `lam` such that the new circumcenter is `lam P`.

Then the new circumcircle is tangent to the original unit circle.
-/
theorem candidate
    (P : Point)
    (lam : ℝ)
    (hlam : lam ≠ 0)
    (hP : OnUnitCircle P) :
    TangentToUnitAt
      (scale lam P)
      ((1 - lam) ^ 2)
      P :=
