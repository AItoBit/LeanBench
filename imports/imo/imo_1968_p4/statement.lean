/--
Formalization of the solution of IMO 1968 Problem 4.
If `a, b, c, d, e, f` are the edge lengths of a tetrahedron, they form 4 triangular faces.
Without loss of generality, we can assume `a` is the maximum edge length.
We prove that either the vertex with edges `a, c, e` or the vertex with edges `a, b, f`
satisfies the condition that its three meeting edges form a triangle.
-/
theorem candidate
  (a b c d e f : ℝ)
  (face1 : a + b > c ∧ b + c > a ∧ c + a > b)
  (face2 : a + e > f ∧ e + f > a ∧ f + a > e)
  (face3 : b + d > f ∧ d + f > b ∧ f + b > d)
  (_face4 : c + d > e ∧ d + e > c ∧ e + c > d)
  (hmax_b : a ≥ b)
  (_hmax_c : a ≥ c)
  (hmax_d : a ≥ d)
  (_hmax_e : a ≥ e)
  (_hmax_f : a ≥ f) :
  (b + c > d ∧ c + d > b ∧ d + b > c) ∨
  (a + c > e ∧ c + e > a ∧ e + a > c) ∨
  (a + b > f ∧ b + f > a ∧ f + a > b) ∨
  (d + e > f ∧ e + f > d ∧ f + d > e) :=
