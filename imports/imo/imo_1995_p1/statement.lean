/--
Coordinate-normalized form of IMO 1995, Problem 1.

The four collinear points are
`A = (0,0)`, `B = (b,0)`, `C = (1,0)`, and `D = (d,0)`, with
`0 < b < 1 < d`.  The radical axis of the circles with diameters `AC` and
`BD` is the vertical line `x = z`; its equation is
`(b + d - 1) z = b d`.  We write `P = (z,t)`, where `t ≠ 0` expresses
`P ≠ Z`.

The equations `hMline`, `hMcircle`, `hNline`, and `hNcircle` say respectively
that `C,P,M` are collinear, `M` is on the circle with diameter `AC`, `B,P,N`
are collinear, and `N` is on the circle with diameter `BD`.  The two
inequalities exclude the already known intersections `M = C` and `N = B`.

The conclusion constructs a real `q` such that `Q = (z,q)` lies on both
`AM` and `DN`; since it also lies on `x = z = XY`, the three lines are
concurrent.
-/
theorem candidate
    (b d z t mx my nx ny : ℝ)
    (_hb : 0 < b) (hbc : b < 1) (hcd : 1 < d) (ht : t ≠ 0)
    (hradical : (b + d - 1) * z = b * d)
    (hMline : (mx - 1) * t - my * (z - 1) = 0)
    (hMcircle : mx * (mx - 1) + my ^ 2 = 0)
    (hMneC : (mx, my) ≠ (1, 0))
    (hNline : (nx - b) * t - ny * (z - b) = 0)
    (hNcircle : (nx - b) * (nx - d) + ny ^ 2 = 0)
    (hNneB : (nx, ny) ≠ (b, 0)) :
    ∃ q : ℝ,
      z * my - q * mx = 0 ∧
      (z - d) * ny - q * (nx - d) = 0 :=
