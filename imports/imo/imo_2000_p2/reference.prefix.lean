namespace Imo2000P2

/-- The substituted form: `(x-y+z)(y-z+x)(z-x+y) ≤ xyz` for positive `x, y, z`. -/
theorem core (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (x - y + z) * (y - z + x) * (z - x + y) ≤ x * y * z := by
  rcases le_or_lt (x - y + z) 0 with hp | hp
  · -- `p ≤ 0`, so `q, r > 0` and the product is nonpositive
    have hq : 0 < y - z + x := by linarith
    have hr : 0 < z - x + y := by linarith
    nlinarith [mul_pos hq hr, mul_pos (mul_pos hx hy) hz]
  rcases le_or_lt (y - z + x) 0 with hq | hq
  · have hr : 0 < z - x + y := by linarith
    nlinarith [mul_pos hr hp, mul_pos (mul_pos hx hy) hz]
  rcases le_or_lt (z - x + y) 0 with hr | hr
  · nlinarith [mul_pos hp hq, mul_pos (mul_pos hx hy) hz]
  -- all three are positive
  have h1 : (x - y + z) * (y - z + x) ≤ x ^ 2 := by nlinarith [sq_nonneg (y - z)]
  have h2 : (y - z + x) * (z - x + y) ≤ y ^ 2 := by nlinarith [sq_nonneg (x - z)]
  have h3 : (z - x + y) * (x - y + z) ≤ z ^ 2 := by nlinarith [sq_nonneg (x - y)]
  have hqr : 0 < (y - z + x) * (z - x + y) := mul_pos hq hr
  have hrp : 0 < (z - x + y) * (x - y + z) := mul_pos hr hp
  have hprod : ((x - y + z) * (y - z + x) * (z - x + y)) ^ 2 ≤ (x * y * z) ^ 2 := by
    calc ((x - y + z) * (y - z + x) * (z - x + y)) ^ 2
        = ((x - y + z) * (y - z + x)) * ((y - z + x) * (z - x + y)) *
            ((z - x + y) * (x - y + z)) := by ring
      _ ≤ x ^ 2 * y ^ 2 * z ^ 2 := by
          refine mul_le_mul (mul_le_mul h1 h2 hqr.le (by positivity)) h3 hrp.le (by positivity)
      _ = (x * y * z) ^ 2 := by ring
  have hpos : 0 < (x - y + z) * (y - z + x) * (z - x + y) := mul_pos (mul_pos hp hq) hr
  nlinarith [hprod, hpos, mul_pos (mul_pos hx hy) hz]
