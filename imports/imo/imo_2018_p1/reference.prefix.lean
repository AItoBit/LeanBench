namespace Imo2018P1

/-- The Euclidean plane. -/
abbrev Pt := ℝ × ℝ

/-- The standard inner product. -/
def dotp (x y : Pt) : ℝ := x.1 * y.1 + x.2 * y.2

/-- The scalar cross product. `crossp x y = 0` exactly when `x` and `y` are parallel. -/
def crossp (x y : Pt) : ℝ := x.1 * y.2 - x.2 * y.1

/-- Lagrange's identity in the plane: `|y|²|x|² = (x·y)² + (y × x)²`. -/
lemma lagrange (x y : Pt) : dotp y y * dotp x x = dotp x y ^ 2 + crossp y x ^ 2 := by
  simp only [dotp, crossp]; ring

/-- Resolving `x` along the orthogonal basis `(y, yᗮ)` and taking `crossp z ·`. -/
lemma cross_decomp (x y z : Pt) :
    dotp y y * crossp z x = dotp x y * crossp z y + crossp y x * dotp z y := by
  simp only [dotp, crossp]; ring

/-- The scalar heart of the problem. -/
lemma core {p q l m X Y cr k k' R : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hl0 : 0 < l) (hl1 : l < 1) (hm0 : 0 < m) (hm1 : m < 1)
    (hS : l ^ 2 * p = m ^ 2 * q)
    (hX2 : X ^ 2 = p * R ^ 2 - l ^ 2 * p ^ 2 / 4)
    (hY2 : Y ^ 2 = q * R ^ 2 - m ^ 2 * q ^ 2 / 4)
    (hk2 : k ^ 2 = p * R ^ 2 - p ^ 2 / 4)
    (hk'2 : k' ^ 2 = q * R ^ 2 - q ^ 2 / 4)
    (hcr : cr ≠ 0)
    (hAF : (X - k) * cr < 0)
    (hAG : 0 < (Y - k') * cr) :
    m * Y + l * X = 0 ∧ m * q * X + l * p * Y = 0 := by
  -- `X² > k²` and `Y² > k'²`, because `l, m < 1`.
  have hXk : 0 < (X - k) * (X + k) := by
    have hfac : (X - k) * (X + k) = p ^ 2 * (1 - l ^ 2) / 4 := by
      linear_combination hX2 - hk2
    have h1 : 0 < 1 - l ^ 2 := by nlinarith
    have h2 : 0 < p * p := mul_pos hp hp
    rw [hfac]
    nlinarith [mul_pos h2 h1]
  have hYk : 0 < (Y - k') * (Y + k') := by
    have hfac : (Y - k') * (Y + k') = q ^ 2 * (1 - m ^ 2) / 4 := by
      linear_combination hY2 - hk'2
    have h1 : 0 < 1 - m ^ 2 := by nlinarith
    have h2 : 0 < q * q := mul_pos hq hq
    rw [hfac]
    nlinarith [mul_pos h2 h1]
  -- Hence `X` and `Y` sit on opposite sides.
  have hXcr : X * cr < 0 := by
    rcases lt_or_gt_of_ne hcr with h | h
    · have h1 : 0 < X - k := by nlinarith
      have h2 : 0 < X + k := by
        by_contra hcon
        have hc : X + k ≤ 0 := not_lt.mp hcon
        nlinarith
      exact mul_neg_of_pos_of_neg (by linarith) h
    · have h1 : X - k < 0 := by nlinarith
      have h2 : X + k < 0 := by
        by_contra hcon
        have hc : 0 ≤ X + k := not_lt.mp hcon
        nlinarith
      exact mul_neg_of_neg_of_pos (by linarith) h
  have hYcr : 0 < Y * cr := by
    rcases lt_or_gt_of_ne hcr with h | h
    · have h1 : Y - k' < 0 := by nlinarith
      have h2 : Y + k' < 0 := by
        by_contra hcon
        have hc : 0 ≤ Y + k' := not_lt.mp hcon
        nlinarith
      exact mul_pos_of_neg_of_neg (by linarith) h
    · have h1 : 0 < Y - k' := by nlinarith
      have h2 : 0 < Y + k' := by
        by_contra hcon
        have hc : Y + k' ≤ 0 := not_lt.mp hcon
        nlinarith
      exact mul_pos (by linarith) h
  have hcr2 : 0 < cr ^ 2 := by positivity
  have hXY : X * Y < 0 := by
    have h3 : X * cr * (Y * cr) < 0 := mul_neg_of_neg_of_pos hXcr hYcr
    nlinarith
  -- `m²Y² = l²X²` is pure algebra.
  have hmsq : m ^ 2 * Y ^ 2 = l ^ 2 * X ^ 2 := by
    rw [hX2, hY2]
    linear_combination (-(R ^ 2) + (m ^ 2 * q + l ^ 2 * p) / 4) * hS
  have hMY : m * Y + l * X = 0 := by
    have hfac : (m * Y + l * X) * (m * Y - l * X) = 0 := by linear_combination hmsq
    rcases mul_eq_zero.mp hfac with h | h
    · exact h
    · exfalso
      have hlm : 0 < l * m := mul_pos hl0 hm0
      nlinarith [sq_nonneg (l * X)]
  refine ⟨hMY, ?_⟩
  have h4 : m * (m * q * X + l * p * Y) = 0 := by
    linear_combination (l * p) * hMY - X * hS
  rcases mul_eq_zero.mp h4 with h | h
  · exact absurd h (ne_of_gt hm0)
  · exact h
