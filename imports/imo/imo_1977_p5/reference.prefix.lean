set_option maxRecDepth 10000

namespace Imo1977P5

/-- `q ≤ 44`, from `q² ≤ 1977`. -/
private lemma qle {q r : ℤ} (hq0 : 0 ≤ q) (hr0 : 0 ≤ r) (h : q ^ 2 + r = 1977) :
    q ≤ 44 := by
  nlinarith

/-- `a + b ≤ 2q + 1`, from `(a+b)² ≤ 2(a²+b²) = 2(q(a+b)+r) < 2(q+1)(a+b)`. -/
private lemma abbound {a b q r : ℤ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hr : r < a + b)
    (h : a ^ 2 + b ^ 2 = q * (a + b) + r) : a + b ≤ 2 * q + 1 := by
  nlinarith [sq_nonneg (a - b)]

/-- `q ≥ 44`, from `1977 = q² + r < q² + 2q + 1`. -/
private lemma qge {a b q r : ℤ} (hq0 : 0 ≤ q) (h : q ^ 2 + r = 1977)
    (hr : r < a + b) (hab : a + b ≤ 2 * q + 1) : 44 ≤ q := by
  nlinarith

/-- From `x² + y² = 1009` and `32² = 1024`, we get `x ≤ 31`. -/
private lemma sq_bound {x y : ℤ} (h : x ^ 2 + y ^ 2 = 1009) : x ≤ 31 := by
  nlinarith [sq_nonneg y]

set_option maxHeartbeats 1000000 in
/-- The finite search: the only solutions of `a² + b² = 44(a+b) + 41` with
`a, b ≤ 53` are the four expected pairs. -/
private lemma enum : ∀ a ∈ Finset.range 54, ∀ b ∈ Finset.range 54,
    a ^ 2 + b ^ 2 = 44 * (a + b) + 41 →
      (a = 50 ∧ b = 37) ∨ (a = 37 ∧ b = 50) ∨ (a = 50 ∧ b = 7) ∨ (a = 7 ∧ b = 50) := by
  decide
