/--
Formalization of the algebraic core of IMO 1969 Problem 2, Solution 2.
The function f(x) can be rewritten using the cosine addition formula as
A * cos x - B * sin x, where A and B depend on the constants a_i.
If x₁ and x₂ are roots of this function, we show that sin(x₂ - x₁) = 0.
This implies their difference is a multiple of π, as required.
-/
theorem candidate (A B x₁ x₂ : ℝ)
    (h_non_zero : A^2 + B^2 > 0)
    (hx₁ : A * cos x₁ - B * sin x₁ = 0)
    (hx₂ : A * cos x₂ - B * sin x₂ = 0) :
    sin (x₂ - x₁) = 0 :=
