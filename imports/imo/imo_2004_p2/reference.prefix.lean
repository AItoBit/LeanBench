namespace Imo2004P2

open Polynomial

/-- Scaling the variable scales the coefficients. -/
theorem coeff_comp_C_mul_X (f : ℝ[X]) (r : ℝ) (n : ℕ) :
    (f.comp (C r * X)).coeff n = f.coeff n * r ^ n := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [add_comp, coeff_add, hp, hq, coeff_add, add_mul]
  | monomial m a =>
      have h1 : (monomial m a).comp (C r * X) = monomial m (a * r ^ m) := by
        rw [monomial_comp, mul_pow, ← C_pow, ← mul_assoc, ← C_mul, C_mul_X_pow_eq_monomial]
      rw [h1, coeff_monomial, coeff_monomial]
      split_ifs with h
      · rw [h]
      · ring

/-- `8ⁿ` overtakes `2·7ⁿ` from `n = 6` on. -/
theorem two_mul_seven_pow_lt (n : ℕ) (hn : 6 ≤ n) : 2 * 7 ^ n < 8 ^ n := by
  induction n with
  | zero => omega
  | succ m ih =>
      rcases Nat.lt_or_ge m 6 with h | h
      · have hm : m = 5 := by omega
        subst hm
        norm_num
      · have h1 := ih h
        have hpos : (0 : ℕ) < 8 ^ m := pow_pos (by norm_num) m
        have e1 : 2 * 7 ^ (m + 1) = 7 * (2 * 7 ^ m) := by ring
        have e2 : (8 : ℕ) ^ (m + 1) = 8 * 8 ^ m := by ring
        omega
