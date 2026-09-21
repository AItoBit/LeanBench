/-- The key step: if the product of the two roots is at least `a²`, the pair is `(n, 2n)`. -/
theorem key {a b k : ℤ} (ha : 0 < a) (hb : 1 < b) (hk : 0 < k)
    (hak : a ^ 2 = k * (2 * a * b ^ 2 - b ^ 3 + 1))
    (hle : a ^ 2 ≤ k * (b ^ 3 - 1)) :
    b = 2 * a ∧ k = a ^ 2 := by
  have ha2 : 0 < a ^ 2 := by positivity
  have hb2sq : 0 < b ^ 2 := by positivity
  have hb2four : (4 : ℤ) ≤ b ^ 2 := by nlinarith
  -- the denominator is positive
  have hDpos : 0 < 2 * a * b ^ 2 - b ^ 3 + 1 := by
    by_contra hcon
    push Not at hcon
    nlinarith [hak, hk, ha2, hcon]
  -- `D ≤ b³ - 1`, hence `a < b`
  have h1 : 2 * a * b ^ 2 - b ^ 3 + 1 ≤ b ^ 3 - 1 := by
    have h0 : k * (2 * a * b ^ 2 - b ^ 3 + 1) ≤ k * (b ^ 3 - 1) := by linarith [hak, hle]
    exact le_of_mul_le_mul_left h0 hk
  have hab : a < b := by nlinarith [h1, hb2sq]
  -- `D ≤ a² < b²`
  have hDa : 2 * a * b ^ 2 - b ^ 3 + 1 ≤ a ^ 2 := by nlinarith [hak, hk, hDpos]
  have hab2 : a ^ 2 < b ^ 2 := by nlinarith [hab, ha]
  -- `0 < (2a - b)b² + 1 < b²` pins `2a = b`
  have hge : 0 ≤ 2 * a - b := by
    by_contra hcon
    push Not at hcon
    have h3 : 2 * a - b ≤ -1 := by omega
    have hprod : 0 ≤ (-1 - (2 * a - b)) * b ^ 2 := mul_nonneg (by linarith) (by positivity)
    nlinarith [hDpos, hb2four, hprod]
  have hle2 : 2 * a - b ≤ 0 := by
    by_contra hcon
    push Not at hcon
    have h3 : 1 ≤ 2 * a - b := by omega
    have hprod : 0 ≤ (2 * a - b - 1) * b ^ 2 := mul_nonneg (by linarith) (by positivity)
    nlinarith [hDa, hab2, hprod]
  have hbe : b = 2 * a := by omega
  refine ⟨hbe, ?_⟩
  subst hbe
  linear_combination -hak
