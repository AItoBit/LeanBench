namespace IMO1987P2

theorem candidate
    (KM BC AL AN Area_AKNM Area_ABC : ℝ)
    (h_BC_pos : BC ≠ 0)
    (h_AN_pos : AN ≠ 0)
    (h_ratio : KM / BC = AL / AN)
    (h_area_quad : Area_AKNM = (1 / 2) * KM * AN)
    (h_area_tri : Area_ABC = (1 / 2) * BC * AL) :
    Area_AKNM = Area_ABC :=
