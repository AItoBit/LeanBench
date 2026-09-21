/-- Both moving points start at `A`. -/
theorem imo1979P3Motion_zero (O A : ℂ) : imo1979P3Motion O A 0 = A := by
  simp [imo1979P3Motion]

/-- Both moving points are back at `A` after one revolution. -/
theorem imo1979P3Motion_one (O A : ℂ) : imo1979P3Motion O A 1 = A := by
  simp [imo1979P3Motion, Complex.exp_two_pi_mul_I]

/-- A moving point indeed travels on the circle centred at `O` through `A`. -/
theorem dist_imo1979P3Motion_center (O A : ℂ) (t : ℝ) :
    dist (imo1979P3Motion O A t) O = dist A O := by
  rw [Complex.dist_eq, Complex.dist_eq, imo1979P3Motion]
  have h0 : O + (A - O) * Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I) - O
      = (A - O) * Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I) := by ring
  rw [h0, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- The purely algebraic identity underlying the solution. -/
private theorem key_identity (r₁ s₁ r₂ s₂ x y u v N : ℂ) (hu : u * v = 1)
    (hx : x * (s₁ - s₂) = N) (hy : y * (r₁ - r₂) = N) (hN : N = r₂ * s₂ - r₁ * s₁) :
    (r₁ * (u - 1) - x) * (s₁ * (v - 1) - y) = (r₂ * (u - 1) - x) * (s₂ * (v - 1) - y) := by
  linear_combination (r₁ * s₁ - r₂ * s₂) * hu + (1 - v) * hx + (1 - u) * hy +
    (2 - u - v) * hN
