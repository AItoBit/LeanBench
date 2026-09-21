/-- **IMO 1975, Problem 6.**  For a positive integer `n`, the two-variable real polynomials `P`
which are homogeneous of degree `n`, satisfy `P (b + c, a) + P (c + a, b) + P (a + b, c) = 0`
for all real `a, b, c`, and satisfy `P (1, 0) = 1`, are exactly `(x - 2 y) (x + y) ^ (n - 1)`. -/
theorem candidate (n : ℕ) (hn : 0 < n) (P : MvPolynomial (Fin 2) ℝ) :
    ((∀ t x y : ℝ, ev P (t * x) (t * y) = t ^ n * ev P x y) ∧
      (∀ a b c : ℝ, ev P (b + c) a + ev P (c + a) b + ev P (a + b) c = 0) ∧
      ev P 1 0 = 1) ↔
      P = (X 0 - 2 * X 1) * (X 0 + X 1) ^ (n - 1) :=
