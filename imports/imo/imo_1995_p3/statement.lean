/-- **No two labels can be equal.**  Suppose `U` and `V` carry the same label,
so that for each of the three pairs taken from `X`, `Y`, `Z` the triangles on
that pair with apex `U` and with apex `V` have equal areas.  If `X`, `Y`, `Z`
are not collinear and none of `X`, `Y`, `Z` is collinear with `U` and `V`, this
is impossible. -/
theorem candidate {X Y Z U V : ℝ × ℝ}
    (hXYZ : sdet X Y Z ≠ 0) (hXUV : sdet X U V ≠ 0) (hYUV : sdet Y U V ≠ 0)
    (hZUV : sdet Z U V ≠ 0)
    (h₁ : area X Y U = area X Y V) (h₂ : area X Z U = area X Z V)
    (h₃ : area Y Z U = area Y Z V) : False :=
