theorem abs_le_of_sq_le_sq {u K : ℝ} (h : u ^ 2 ≤ K ^ 2) (hK : 0 ≤ K) : |u| ≤ K := by
  nlinarith [abs_nonneg u, sq_abs u, h, hK]

/-- The inequality after the substitution `s = a+b+c`, `x = a-b`, `y = b-c`. -/
theorem core_swy (s x y : ℝ) :
    512 * (s * (x * y * (x + y))) ^ 2 ≤ 81 * ((s ^ 2 + 2 * (x ^ 2 + x * y + y ^ 2)) / 3) ^ 4 := by
  have hA : (0 : ℝ) ≤ s ^ 2 := sq_nonneg s
  have hv : (0 : ℝ) ≤ 2 * (x ^ 2 + x * y + y ^ 2) := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (x + y)]
  -- `27 w² ≤ 4(x²+xy+y²)³`
  have hw : 27 * (x * y * (x + y)) ^ 2 ≤ 4 * (x ^ 2 + x * y + y ^ 2) ^ 3 := by
    nlinarith [sq_nonneg ((x - y) * (2 * x + y) * (x + 2 * y))]
  have h1 : 54 * (x * y * (x + y)) ^ 2 ≤ (2 * (x ^ 2 + x * y + y ^ 2)) ^ 3 := by nlinarith [hw]
  -- `256 A v³ ≤ 27 (A+v)⁴`
  have hQ : (0 : ℝ) ≤ 3 * (s ^ 2) ^ 2 + 14 * (s ^ 2) * (2 * (x ^ 2 + x * y + y ^ 2))
      + 27 * (2 * (x ^ 2 + x * y + y ^ 2)) ^ 2 := by
    nlinarith [sq_nonneg (s ^ 2), mul_nonneg hA hv, sq_nonneg (2 * (x ^ 2 + x * y + y ^ 2))]
  have h2 : 256 * (s ^ 2) * (2 * (x ^ 2 + x * y + y ^ 2)) ^ 3
      ≤ 27 * ((s ^ 2) + 2 * (x ^ 2 + x * y + y ^ 2)) ^ 4 := by
    nlinarith [mul_nonneg (sq_nonneg (3 * (s ^ 2) - 2 * (x ^ 2 + x * y + y ^ 2))) hQ]
  have h3 : (s ^ 2) * (54 * (x * y * (x + y)) ^ 2)
      ≤ (s ^ 2) * ((2 * (x ^ 2 + x * y + y ^ 2)) ^ 3) :=
    mul_le_mul_of_nonneg_left h1 hA
  nlinarith [h3, h2]

theorem core (a b c : ℝ) :
    512 * (a * b * (a ^ 2 - b ^ 2) + b * c * (b ^ 2 - c ^ 2) + c * a * (c ^ 2 - a ^ 2)) ^ 2
      ≤ 81 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 4 := by
  have h1 : a * b * (a ^ 2 - b ^ 2) + b * c * (b ^ 2 - c ^ 2) + c * a * (c ^ 2 - a ^ 2)
      = (a + b + c) * ((a - b) * (b - c) * ((a - b) + (b - c))) := by ring
  have h2 : a ^ 2 + b ^ 2 + c ^ 2
      = ((a + b + c) ^ 2 + 2 * ((a - b) ^ 2 + (a - b) * (b - c) + (b - c) ^ 2)) / 3 := by ring
  rw [h1, h2]
  exact core_swy (a + b + c) (a - b) (b - c)
