/--
IMO 1963 Problem 4: find all `(x₁, …, x₅)` for which there is a real `y` with
`xᵢ + xᵢ₊₂ = y * xᵢ₊₁` for all `i` (indices reduced mod 5).

The solutions are exactly the constant tuples `(a, a, a, a, a)` (which come from `y = 2`,
and include the zero tuple, the only solution for all other values of `y`)
together with the two-parameter families `(a, b, -a + y*b, -y*a - y*b, y*a - b)`
for `y = (-1 ± √5)/2`.
-/
theorem candidate :
    {(x₁, x₂, x₃, x₄, x₅) |
      (x₁ : ℝ) (x₂ : ℝ) (x₃ : ℝ) (x₄ : ℝ) (x₅ : ℝ) (y : ℝ)
      (_h₀ : x₅ + x₂ = y*x₁)
      (_h₁ : x₁ + x₃ = y*x₂)
      (_h₂ : x₂ + x₄ = y*x₃)
      (_h₃ : x₃ + x₅ = y*x₄)
      (_h₄ : x₄ + x₁ = y*x₅)} =
      ({(a, a, a, a, a) | (a : ℝ)} ∪
      {(a, b, -a + y*b, -y*a - y*b, y*a - b) |
        (a : ℝ) (b : ℝ) (y : ℝ)
        (_h₀ : y = (-1 + √5) / 2 ∨ y = (-1 - √5) / 2)}) :=
