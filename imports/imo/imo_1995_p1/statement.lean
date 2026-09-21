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
