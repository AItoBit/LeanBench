open Real

namespace Imo1989P4

/-- Two circles of radii `ρ₁`, `ρ₂` with centres at heights `ρ₁`, `ρ₂` above a line and
externally tangent to each other have squared horizontal offset `4ρ₁ρ₂`. -/
theorem sq_of_tangent {r₁ r₂ u v : ℝ}
    (h : Real.sqrt ((u - v) ^ 2 + (r₁ - r₂) ^ 2) = r₁ + r₂) :
    (u - v) ^ 2 = 4 * (r₁ * r₂) := by
  have hsq : (u - v) ^ 2 + (r₁ - r₂) ^ 2 = (r₁ + r₂) ^ 2 := by
    have h0 : (0 : ℝ) ≤ (u - v) ^ 2 + (r₁ - r₂) ^ 2 := by positivity
    calc (u - v) ^ 2 + (r₁ - r₂) ^ 2
        = Real.sqrt ((u - v) ^ 2 + (r₁ - r₂) ^ 2) ^ 2 := (Real.sq_sqrt h0).symm
      _ = (r₁ + r₂) ^ 2 := by rw [h]
  nlinarith [hsq]

/-- **Metric core of IMO 1989 P4.** -/
theorem imo1989_p4_core {a b h : ℝ} (ha : 0 < a) (hb : 0 < b) (hh : 0 < h)
    (hle : Real.sqrt (a * h) + Real.sqrt (b * h) ≤ Real.sqrt (a * b)) :
    1 / Real.sqrt a + 1 / Real.sqrt b ≤ 1 / Real.sqrt h := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  have hsh : 0 < Real.sqrt h := Real.sqrt_pos.2 hh
  rw [Real.sqrt_mul ha.le, Real.sqrt_mul hb.le, Real.sqrt_mul ha.le] at hle
  rw [div_add_div _ _ hsa.ne' hsb.ne', div_le_div_iff₀ (by positivity) hsh]
  nlinarith [hle, hsa, hsb, hsh]
