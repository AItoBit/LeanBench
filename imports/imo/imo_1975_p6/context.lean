open scoped BigOperators

open scoped Real

open scoped Nat

open scoped Classical

open scoped Pointwise

set_option maxHeartbeats 8000000

set_option maxRecDepth 4000

set_option synthInstance.maxHeartbeats 20000

set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false

set_option autoImplicit false

set_option grind.warning false

/-!
# IMO 1975, Problem 6

Find all polynomials `P` in two variables such that

* (i) for a positive integer `n` and all real `t, x, y`, `P (t x, t y) = tⁿ P (x, y)`
  (that is, `P` is homogeneous of degree `n`);
* (ii) for all real `a, b, c`, `P (b + c, a) + P (c + a, b) + P (a + b, c) = 0`;
* (iii) `P (1, 0) = 1`.

The answer is `P (x, y) = (x - 2 y) (x + y) ^ (n - 1)`.
-/

namespace Imo1975P6

open MvPolynomial

noncomputable section

/-- Evaluation of a two-variable real polynomial at a point `(x, y)`. -/
def ev (P : MvPolynomial (Fin 2) ℝ) (x y : ℝ) : ℝ := eval ![x, y] P

/-- Substitution `x ↦ -y`, `y ↦ y`. -/
def antidiag (P : MvPolynomial (Fin 2) ℝ) : MvPolynomial (Fin 2) ℝ := bind₁ ![-X 1, X 1] P

/-- The three-variable polynomial `P (b + c, a) + P (c + a, b) + P (a + b, c)`. -/
def cyc (P : MvPolynomial (Fin 2) ℝ) : MvPolynomial (Fin 3) ℝ :=
  bind₁ ![X 1 + X 2, X 0] P + bind₁ ![X 2 + X 0, X 1] P + bind₁ ![X 0 + X 1, X 2] P

/-- Substitution `x ↦ t x`, `y ↦ t y`. -/
def scal (t : ℝ) (P : MvPolynomial (Fin 2) ℝ) : MvPolynomial (Fin 2) ℝ :=
  bind₁ ![C t * X 0, C t * X 1] P
