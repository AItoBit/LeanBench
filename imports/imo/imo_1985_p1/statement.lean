theorem candidate
    (r xA yA xB yB : ℝ)
    (hA_unit : xA^2 + yA^2 = 1)
    (hB_unit : xB^2 + yB^2 = 1)
    (hxA : xA ≠ 0) (hyA : yA ≠ 0)
    (hxB : xB ≠ 0) (hyB : yB ≠ 0) :
    (r * ((2 * yA^2 - 1) / (2 * xA * yA)) + r * (xB / yB)) + 
    (r * ((2 * yB^2 - 1) / (2 * xB * yB)) + r * (xA / yA)) = 
    r * (1 / (2 * xA * yA)) + r * (1 / (2 * xB * yB)) :=
