/-- **The metric core of IMO 1996 P2:** the angle hypothesis forces `AC · PB = AB · PC`. -/
theorem candidate (a b c p : ℂ)
    (hT : (c - p) * (a - b) ≠ 0)
    (hX : (a - p) * (b - c) ≠ 0)
    (hnr : (((b - p) * (c - a)) / ((c - p) * (a - b))).im ≠ 0)
    (hcond : ((((b - p) * (c - a)) * ((c - p) * (a - b)))
        / ((a - p) * (b - c)) ^ 2).im = 0) :
    ‖b - p‖ * ‖c - a‖ = ‖c - p‖ * ‖a - b‖ :=
