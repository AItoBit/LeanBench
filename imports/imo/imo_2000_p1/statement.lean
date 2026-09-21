/-- **IMO 2000 P1.** -/
theorem candidate
    (a b r₁ r₂ m₁ m₂ n₁ n₂ ex ey px qx : ℝ)
    (hab : a ≠ b) (hm₂ : m₂ ≠ 0) (hn₂ : n₂ ≠ 0)
    -- `M` lies on `G₁` (centre `(a, r₁)`, tangent to the `x`-axis at `A = (a,0)`) and on `G₂`
    (hM1 : (m₁ - a) ^ 2 + m₂ ^ 2 = 2 * r₁ * m₂)
    (hM2 : (m₁ - b) ^ 2 + m₂ ^ 2 = 2 * r₂ * m₂)
    -- `N` lies on `G₁` and on `G₂`
    (hN1 : (n₁ - a) ^ 2 + n₂ ^ 2 = 2 * r₁ * n₂)
    (hN2 : (n₁ - b) ^ 2 + n₂ ^ 2 = 2 * r₂ * n₂)
    -- `E` is on line `AC`, where `A = (a,0)` and `C = (2a - m₁, m₂)` is the second meet of
    -- `G₁` with `CD`
    (hE1 : (a - m₁) * ey - m₂ * (ex - a) = 0)
    -- `E` is on line `BD`, where `B = (b,0)` and `D = (2b - m₁, m₂)`
    (hE2 : (b - m₁) * ey - m₂ * (ex - b) = 0)
    -- `P = (px, m₂)` is on line `AN`, and `Q = (qx, m₂)` is on line `BN`
    (hP : (n₁ - a) * m₂ = n₂ * (px - a))
    (hQ : (n₁ - b) * m₂ = n₂ * (qx - b)) :
    dist (⟨ex, ey⟩ : ℂ) (⟨px, m₂⟩ : ℂ) = dist (⟨ex, ey⟩ : ℂ) (⟨qx, m₂⟩ : ℂ) :=
