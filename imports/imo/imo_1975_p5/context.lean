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
# IMO 1975 Problem 5

Determine, with proof, whether or not one can find `1975` points on the circumference of a
circle with unit radius such that the distance between any two of them is a rational number.

The answer is **yes**.  We use the classical construction: let `z = (3 + 4i)/5`, a point of the
unit circle which is not a root of unity, and take the points `z ^ (2 * k)` for `k < 1975`.
The distance between `z ^ (2 * j)` and `z ^ (2 * k)` equals `2 * |Im (z ^ (j - k))|`, which is
rational.
-/

namespace IMO1975P5

/-- The Gaussian integer `(3 + 4i)^n`, recorded as the pair of its real and imaginary parts. -/
def gp : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | (n + 1) => (3 * (gp n).1 - 4 * (gp n).2, 4 * (gp n).1 + 3 * (gp n).2)

/-- The base point of the construction: a point of the unit circle with rational coordinates. -/
noncomputable def z : ℂ := (3 + 4 * Complex.I) / 5

/-- The points of the construction. -/
noncomputable def pt (k : ℕ) : ℂ := z ^ (2 * k)
