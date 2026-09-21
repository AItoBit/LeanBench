/--
Once O is known to lie on the perpendicular bisector of MN,
the desired equality is literally its definition.
-/
theorem candidate
    {O M N : Point}
    (hO :
      OnPerpBisector d O M N) :
    d O M = d O N :=
