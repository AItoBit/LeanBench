open scoped Real

namespace IMO1994P5

/--
The unique solution to IMO 1994 Problem 5 is f(x) = -x / (x + 1).
We formalize the exact algebraic verification that this function satisfies the 
primary functional equation condition on the domain x, y ≠ -1.
-/

noncomputable def f (x : ℝ) : ℝ := -x / (x + 1)

theorem candidate (x y : ℝ) (hx : x + 1 ≠ 0) (hy : y + 1 ≠ 0) :
    f (x + f y + x * f y) = y + f x + y * f x :=
