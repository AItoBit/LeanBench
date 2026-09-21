theorem candidate (y F : ℝ)
    (hy1 : 0 ≤ y) (hy2 : y < 2)
    (hF_pos : 0 < F)
    (h_lower : 2 ≤ (2 - y) * F)
    (h_upper : 2 ≤ y + 2 / F) :
    F = 2 / (2 - y) :=
