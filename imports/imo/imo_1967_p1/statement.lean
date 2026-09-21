open Real

/--
Formalization of the boundary case calculations from the solution to IMO 1967 Problem 1.
  the solution simplifies the geometric
condition to a set of algebraic and trigonometric calculations for the maximum bounding case.
-/

theorem candidate
    (x a α : ℝ)
    (hx_nonneg : 0 ≤ x)
    (h_pythagoras : 1^2 + x^2 = 2^2)
    (h_cos : cos α = 1 / 2)
    (h_sin : sin α = sqrt 3 / 2)
    (h_a_bound : a ≤ cos α + sqrt 3 * sin α) :
    x = sqrt 3 ∧ a ≤ 2 :=
