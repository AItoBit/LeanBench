/--
Compact final statement of the algebraic core.

The Law of Sines gives the cotangent relation,
the side decomposition gives `BC = A+D`,
and therefore the point identified by the source with the
orthocenter lies on `XY` for every parameter `w`.
-/
theorem candidate
    (BC AC AB sinB sinC cosB cosC : ℝ)
    (hsinB :
      sinB ≠ 0)
    (hsinC :
      sinC ≠ 0)
    (hside :
      BC =
        AC * cosC +
        AB * cosB)
    (hsine :
      AC / sinB =
        AB / sinC) :
    ∀ w : ℝ,
      Collinear
        (BC,
          w * (cosB / sinB))
        (0,
          (BC - w) *
            (cosC / sinC))
        (AC * cosC,
          (AB * cosB) *
            (cosC / sinC)) :=
