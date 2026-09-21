/-- The equal-side conditions force the hexagon to be symmetric: `p = q = r`. -/
theorem equal_sides_symmetric {p q r sig t : ℝ} (hsig : 0 < sig)
    (h1 : (sig - p) ^ 2 + q ^ 2 - (sig - p) * q = t ^ 2)
    (h2 : (sig - q) ^ 2 + r ^ 2 - (sig - q) * r = t ^ 2)
    (h3 : (sig - r) ^ 2 + p ^ 2 - (sig - r) * p = t ^ 2) :
    p = q ∧ q = r := by
  set S : ℝ := 2 * (p + q + r) - 3 * sig with hS
  have hD1 : (2 * p - 2 * r) * S = sig * (S - 6 * q + 3 * sig) := by
    rw [hS]; linear_combination 4 * h1 - 4 * h2
  have hD2 : (2 * q - 2 * p) * S = sig * (S - 6 * r + 3 * sig) := by
    rw [hS]; linear_combination 4 * h2 - 4 * h3
  have hD3 : (2 * r - 2 * q) * S = sig * (S - 6 * p + 3 * sig) := by
    rw [hS]; linear_combination 4 * h3 - 4 * h1
  have hpos : 0 < S ^ 2 + 3 * sig ^ 2 := by nlinarith [sq_nonneg S, hsig]
  have hne : S ^ 2 + 3 * sig ^ 2 ≠ 0 := ne_of_gt hpos
  have hp : 3 * (2 * p - sig) - S = 0 := by
    have hk : (3 * (2 * p - sig) - S) * (S ^ 2 + 3 * sig ^ 2) = 0 := by
      linear_combination S * hD1 - S * hD2 + 3 * sig * hD3
    exact (mul_eq_zero.1 hk).resolve_right hne
  have hq : 3 * (2 * q - sig) - S = 0 := by
    have hk : (3 * (2 * q - sig) - S) * (S ^ 2 + 3 * sig ^ 2) = 0 := by
      linear_combination S * hD2 - S * hD3 + 3 * sig * hD1
    exact (mul_eq_zero.1 hk).resolve_right hne
  have hr : 3 * (2 * r - sig) - S = 0 := by
    have hk : (3 * (2 * r - sig) - S) * (S ^ 2 + 3 * sig ^ 2) = 0 := by
      linear_combination S * hD3 - S * hD1 + 3 * sig * hD2
    exact (mul_eq_zero.1 hk).resolve_right hne
  rw [hS] at hp hq hr
  constructor <;> linarith
