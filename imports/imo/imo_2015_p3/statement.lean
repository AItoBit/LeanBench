/--
This packages the final portion of the source proof.

The source has already established:

* `T` is the midpoint of `HA`;
* `N` is the midpoint of `HQ`;
* `TNML` is a rectangle;
* `L` lies on the perpendicular bisector of `AQ`.

The first three imply `ML ∥ AQ`, and the fourth gives
`LA = LQ`.

Hence `ML` is tangent to the circumcircle of `ALQ`.
-/
theorem candidate
    {H A Q T N M L O : Point}
    (hT :
      IsMidpoint T H A)
    (hN :
      IsMidpoint N H Q)
    (hrect :
      OppositeSidesEqual T N M L)
    (hcenter :
      IsCircumcenter O A L Q)
    (hLbisector :
      distSq L A = distSq L Q) :
    TangentAt O L M :=
