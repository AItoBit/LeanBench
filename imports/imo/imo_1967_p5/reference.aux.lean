/--
Auxiliary lemma: (-x)^(2k+1) = - x^(2k+1)
-/
lemma neg_pow_odd (x : ℝ) (k : ℕ) : (-x)^(2 * k + 1) = -(x^(2 * k + 1)) := by
  induction k with
  | zero => ring
  | succ k ih =>
    have h1 : 2 * (k + 1) + 1 = 2 * k + 1 + 2 := by omega
    rw [h1]
    have h2 : (-x) ^ (2 * k + 1 + 2) = (-x) ^ (2 * k + 1) * (-x) ^ 2 := pow_add (-x) _ _
    have h3 : x ^ (2 * k + 1 + 2) = x ^ (2 * k + 1) * x ^ 2 := pow_add x _ _
    rw [h2, h3, ih]
    ring

/--
Auxiliary lemma: x^(2k) ≥ 0
-/
lemma pow_even_nonneg (x : ℝ) (k : ℕ) : 0 ≤ x^(2 * k) := by
  induction k with
  | zero =>
    change 0 ≤ x^0
    rw [pow_zero]
    exact zero_le_one
  | succ k ih =>
    have h1 : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [h1, pow_add]
    have h2 : 0 ≤ x^2 := sq_nonneg x
    exact mul_nonneg ih h2
