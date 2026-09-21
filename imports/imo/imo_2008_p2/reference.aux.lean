/-- The key algebraic identity behind the problem: modulo the constraint `x * y * z = 1`,
the quantity `x²(y-1)²(z-1)² + y²(x-1)²(z-1)² + z²(x-1)²(y-1)² - ((x-1)(y-1)(z-1))²`
is a perfect square. -/
theorem key_identity (x y z : ℝ) (h : x * y * z = 1) :
    x ^ 2 * (y - 1) ^ 2 * (z - 1) ^ 2 + y ^ 2 * (x - 1) ^ 2 * (z - 1) ^ 2 +
        z ^ 2 * (x - 1) ^ 2 * (y - 1) ^ 2 - ((x - 1) * (y - 1) * (z - 1)) ^ 2
      = ((x - 1) * (y - 1) * (z - 1) - x * (y - 1) * (z - 1) - y * (x - 1) * (z - 1) -
          z * (x - 1) * (y - 1)) ^ 2 := by
  linear_combination (-2 * ((x - 1) * (y - 1) * (z - 1))) * h

/-- **IMO 2008, Problem 2 (i).** For real numbers `x, y, z`, all different from `1`, with
`x * y * z = 1`, we have `x²/(x-1)² + y²/(y-1)² + z²/(z-1)² ≥ 1`. -/
theorem sum_sq_div_ge_one (x y z : ℝ) (hx : x ≠ 1) (hy : y ≠ 1) (hz : z ≠ 1)
    (h : x * y * z = 1) :
    1 ≤ x ^ 2 / (x - 1) ^ 2 + y ^ 2 / (y - 1) ^ 2 + z ^ 2 / (z - 1) ^ 2 := by
  have ha : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  have hb : y - 1 ≠ 0 := sub_ne_zero.mpr hy
  have hc : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  have key : x ^ 2 / (x - 1) ^ 2 + y ^ 2 / (y - 1) ^ 2 + z ^ 2 / (z - 1) ^ 2 - 1
      = (((x - 1) * (y - 1) * (z - 1) - x * (y - 1) * (z - 1) - y * (x - 1) * (z - 1) -
          z * (x - 1) * (y - 1)) / ((x - 1) * (y - 1) * (z - 1))) ^ 2 := by
    rw [div_pow, eq_div_iff (by positivity)]
    field_simp
    linear_combination key_identity x y z h
  nlinarith [sq_nonneg (((x - 1) * (y - 1) * (z - 1) - x * (y - 1) * (z - 1) -
    y * (x - 1) * (z - 1) - z * (x - 1) * (y - 1)) / ((x - 1) * (y - 1) * (z - 1)))]

/-- Every member of the family `tripleOf k` (for `k ≠ ±1`) lies in `equalitySet`. -/
theorem tripleOf_mem (k : ℚ) (h1 : k ≠ 1) (h2 : k ≠ -1) : tripleOf k ∈ equalitySet := by
  have ha : k - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hb : k + 1 ≠ 0 := fun h => h2 (by linarith)
  have hs : k ^ 2 + 3 ≠ 0 := by positivity
  have e1 : (1 - k ^ 2) / 4 - 1 = -(k ^ 2 + 3) / 4 := by ring
  have e2 : -2 * (k + 1) / (k - 1) ^ 2 - 1 = -(k ^ 2 + 3) / (k - 1) ^ 2 := by field_simp; ring
  have e3 : 2 * (k - 1) / (k + 1) ^ 2 - 1 = -(k ^ 2 + 3) / (k + 1) ^ 2 := by field_simp; ring
  simp only [equalitySet, tripleOf, Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hs
    rw [h] at e1
    field_simp at e1
    linarith
  · intro h
    apply hs
    rw [h] at e2
    field_simp at e2
    linarith
  · intro h
    apply hs
    rw [h] at e3
    field_simp at e3
    linarith
  · field_simp
    ring
  · rw [e1, e2, e3]
    field_simp
    ring
