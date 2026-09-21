/--
**Problem.** Let `a, b, c` be the sides of a triangle and `α, β, γ` the opposite angles
(so the angles are positive and sum to `π`, and the law of sines holds).
If `a + b = tan (γ/2) * (a * tan α + b * tan β)` then the triangle is isosceles: `a = b`.
(The hypotheses `cos α ≠ 0`, `cos β ≠ 0` express that the tangents occurring in the
statement are defined.)
-/
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
