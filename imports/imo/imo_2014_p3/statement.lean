/--
Final geometric step of IMO 2014 Problem 3.

If

* `G` is the circumcenter of triangle `TSH`,
* `G` lies on `AH`,
* `AH ⟂ BD`,

then `BD` is tangent at `H` to the circumcircle of `TSH`.
-/
theorem candidate
    (A B D H S T G : Point)
    (_hcenter :
      IsCircumcenter G T S H)
    (hGAH :
      LiesOnHA A H G)
    (hAHBD :
      Perpendicular A H B D) :
    TangentAt G H B D :=
