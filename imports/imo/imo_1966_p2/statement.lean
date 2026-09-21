theorem candidate
    (a b c α β γ : ℝ)
    (ha : 0 < a) (_hb : 0 < b) (_hc : 0 < c)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hsum : α + β + γ = Real.pi)
    -- law of sines : a / sin α = b / sin β = c / sin γ
    (hlaw1 : a * Real.sin β = b * Real.sin α)
    (_hlaw2 : b * Real.sin γ = c * Real.sin β)
    -- the tangents appearing below are defined
    (hca : Real.cos α ≠ 0) (hcb : Real.cos β ≠ 0)
    (heq : a + b = Real.tan (γ / 2) * (a * Real.tan α + b * Real.tan β)) :
    a = b :=
