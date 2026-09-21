namespace Imo1982P2

/-- The meeting point of the tangents to the unit circle at the unit points `v`
and `w` is `2vw/(v+w)`: it lies on both tangents `z + v² z̄ = 2v` and
`z + w² z̄ = 2w`. -/
theorem vertex_on_tangents (v w : ℂ) (hv : v * (starRingEnd ℂ) v = 1)
    (hw : w * (starRingEnd ℂ) w = 1) (hvw : v + w ≠ 0) :
    (2 * v * w / (v + w)) + v ^ 2 * (starRingEnd ℂ) (2 * v * w / (v + w)) = 2 * v ∧
    (2 * v * w / (v + w)) + w ^ 2 * (starRingEnd ℂ) (2 * v * w / (v + w)) = 2 * w := by
  have hv0 : v ≠ 0 := by intro h; rw [h] at hv; simp at hv
  have hw0 : w ≠ 0 := by intro h; rw [h] at hw; simp at hw
  have cv : (starRingEnd ℂ) v = 1 / v := by field_simp; linear_combination hv
  have cw : (starRingEnd ℂ) w = 1 / w := by field_simp; linear_combination hw
  have hc : (starRingEnd ℂ) (2 * v * w / (v + w)) = 2 / (v + w) := by
    simp only [map_div₀, map_mul, map_add, map_ofNat, cv, cw]
    field_simp
    rw [← add_mul, mul_inv_cancel₀ hvw]
  rw [hc]
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-- With the incircle the unit circle at `0`, reflection in the bisector `0A₁`
sends the touch point `u₁` to `u₂u₃/u₁`, which again lies on the incircle. -/
theorem reflection (u₁ u₂ u₃ : ℂ)
    (hu₁ : u₁ * (starRingEnd ℂ) u₁ = 1) (hu₂ : u₂ * (starRingEnd ℂ) u₂ = 1)
    (hu₃ : u₃ * (starRingEnd ℂ) u₃ = 1) (h23 : u₂ + u₃ ≠ 0) :
    (u₂ * u₃ / u₁) * (starRingEnd ℂ) (2 * u₂ * u₃ / (u₂ + u₃))
        = (2 * u₂ * u₃ / (u₂ + u₃)) * (starRingEnd ℂ) u₁ ∧
      (u₂ * u₃ / u₁) * (starRingEnd ℂ) (u₂ * u₃ / u₁) = 1 := by
  have hu10 : u₁ ≠ 0 := by intro h; rw [h] at hu₁; simp at hu₁
  have hu20 : u₂ ≠ 0 := by intro h; rw [h] at hu₂; simp at hu₂
  have hu30 : u₃ ≠ 0 := by intro h; rw [h] at hu₃; simp at hu₃
  have c1 : (starRingEnd ℂ) u₁ = 1 / u₁ := by field_simp; linear_combination hu₁
  have c2 : (starRingEnd ℂ) u₂ = 1 / u₂ := by field_simp; linear_combination hu₂
  have c3 : (starRingEnd ℂ) u₃ = 1 / u₃ := by field_simp; linear_combination hu₃
  have hc : (starRingEnd ℂ) (2 * u₂ * u₃ / (u₂ + u₃)) = 2 / (u₂ + u₃) := by
    simp only [map_div₀, map_mul, map_add, map_ofNat, c2, c3]
    field_simp
    rw [← add_mul, mul_inv_cancel₀ h23]
  constructor
  · rw [hc, c1]
    field_simp
    ring
  · simp only [map_div₀, map_mul, c1, c2, c3]
    field_simp
