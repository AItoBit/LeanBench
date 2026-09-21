by
  -- `e^{2πi/12} = (√3 + i)/2`
  have hz0 : Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 12)
      = ((Real.sqrt 3 : ℂ) + Complex.I) / 2 := by
    have h : 2 * (Real.pi : ℂ) * Complex.I / 12 = ((Real.pi / 6 : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_pi_div_six, Real.sin_pi_div_six]
    push_cast
    ring
  set s : ℂ := ((Real.sqrt 3 : ℝ) : ℂ) with hsdef
  have hs : s ^ 2 = 3 := by
    rw [hsdef, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    norm_num
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have h1 : s = 1 := by linear_combination h
    rw [h1] at hs
    norm_num at hs
  -- the half-diagonal of the dodecagon
  obtain ⟨q, hq⟩ : ∃ q : ℂ, q = (s - 1) * p / 2 := ⟨_, rfl⟩
  have hqne : q ≠ 0 := by
    rw [hq]
    exact div_ne_zero (mul_ne_zero hs1 hp) (by norm_num)
  -- the square in terms of `q`
  have hA2 : A = o + (s + 1) * q := by
    rw [hA, hq]; linear_combination (-(p / 2)) * hs
  have hB2 : B = o + (s + 1) * q * Complex.I := by
    rw [hB, hq]; linear_combination (-(Complex.I * p / 2)) * hs
  have hC2 : C = o - (s + 1) * q := by
    rw [hC, hq]; linear_combination (p / 2) * hs
  have hD2 : D = o - (s + 1) * q * Complex.I := by
    rw [hD, hq]; linear_combination (Complex.I * p / 2) * hs
  -- the four apexes
  have hK2 : K = o - q * (1 + Complex.I) := by
    rw [hK, hA, hB, hq]; linear_combination (s * p / 2) * Complex.I_sq
  have hL2 : L = o + q * (1 - Complex.I) := by
    rw [hL, hB, hC, hq]; linear_combination (-(s * p / 2)) * Complex.I_sq
  have hM2 : M = o + q * (1 + Complex.I) := by
    rw [hM, hC, hD, hq]; linear_combination (-(s * p / 2)) * Complex.I_sq
  have hN2 : N = o - q * (1 - Complex.I) := by
    rw [hN, hD, hA, hq]; linear_combination (s * p / 2) * Complex.I_sq
  -- the twelfth root of unity and its powers
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, ζ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 12) := ⟨_, rfl⟩
  have hz : ζ = (s + Complex.I) / 2 := by rw [hζ, hz0]
  have e0 : ζ ^ 0 = 1 := pow_zero _
  have e1 : ζ ^ 1 = (s + Complex.I) / 2 := by rw [pow_one, hz]
  have e2 : ζ ^ 2 = (1 + s * Complex.I) / 2 := by
    have h : ζ ^ 2 = ζ * ζ := by ring
    rw [h, hz]
    linear_combination hs / 4 + Complex.I_sq / 4
  have e3 : ζ ^ 3 = Complex.I := by
    have h : ζ ^ 3 = ζ ^ 2 * ζ := by ring
    rw [h, e2, hz]
    linear_combination (Complex.I / 4) * hs + (s / 4) * Complex.I_sq
  have e4 : ζ ^ 4 = (-1 + s * Complex.I) / 2 := by
    have h : ζ ^ 4 = ζ ^ 3 * ζ := by ring
    rw [h, e3, hz]
    linear_combination Complex.I_sq / 2
  have e5 : ζ ^ 5 = (-s + Complex.I) / 2 := by
    have h : ζ ^ 5 = ζ ^ 4 * ζ := by ring
    rw [h, e4, hz]
    linear_combination (Complex.I / 4) * hs + (s / 4) * Complex.I_sq
  have e6 : ζ ^ 6 = -1 := by
    have h : ζ ^ 6 = ζ ^ 5 * ζ := by ring
    rw [h, e5, hz]
    linear_combination (-1 / 4 : ℂ) * hs + Complex.I_sq / 4
  have e7 : ζ ^ 7 = (-s - Complex.I) / 2 := by
    have h : ζ ^ 7 = ζ ^ 6 * ζ := by ring
    rw [h, e6, hz]
    ring
  have e8 : ζ ^ 8 = (-1 - s * Complex.I) / 2 := by
    have h : ζ ^ 8 = ζ ^ 7 * ζ := by ring
    rw [h, e7, hz]
    linear_combination (-1 / 4 : ℂ) * hs + (-1 / 4 : ℂ) * Complex.I_sq
  have e9 : ζ ^ 9 = -Complex.I := by
    have h : ζ ^ 9 = ζ ^ 8 * ζ := by ring
    rw [h, e8, hz]
    linear_combination (-Complex.I / 4) * hs + (-s / 4) * Complex.I_sq
  have e10 : ζ ^ 10 = (1 - s * Complex.I) / 2 := by
    have h : ζ ^ 10 = ζ ^ 9 * ζ := by ring
    rw [h, e9, hz]
    linear_combination (-1 / 2 : ℂ) * Complex.I_sq
  have e11 : ζ ^ 11 = (s - Complex.I) / 2 := by
    have h : ζ ^ 11 = ζ ^ 10 * ζ := by ring
    rw [h, e10, hz]
    linear_combination (-Complex.I / 4) * hs + (-s / 4) * Complex.I_sq
  -- the twelve vertices
  refine ⟨q, ζ, hqne, hζ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hL2, hM2, e0]; ring
  · rw [hA2, hN2, e1]; ring
  · rw [hB2, hL2, e2]; ring
  · rw [hM2, hN2, e3]; ring
  · rw [hB2, hK2, e4]; ring
  · rw [hC2, hM2, e5]; ring
  · rw [hN2, hK2, e6]; ring
  · rw [hC2, hL2, e7]; ring
  · rw [hD2, hN2, e8]; ring
  · rw [hK2, hL2, e9]; ring
  · rw [hD2, hM2, e10]; ring
  · rw [hA2, hK2, e11]; ring
