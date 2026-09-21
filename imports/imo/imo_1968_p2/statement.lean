/--

Let P be the product of the digits of a natural number x. We have the constraints:
1. P ≤ x (a known property of the digit product for natural numbers)
2. P ≥ 0 (since digits are non-negative)
3. P = x^2 - 10x - 22 (from the problem statement)

We prove that these constraints uniquely determine x = 12 and P = 2.
-/
theorem candidate (x P : ℤ)
    (hP_le_x : P ≤ x)
    (hP_nonneg : 0 ≤ P)
    (h_eq : P = x^2 - 10 * x - 22) :
    x = 12 ∧ P = 2 :=
