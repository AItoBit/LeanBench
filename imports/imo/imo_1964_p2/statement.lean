/--
IMO 1964 Problem 2: Suppose that `a, b, c` are the sides of a triangle. Then
`a^2 (b + c - a) + b^2 (c + a - b) + c^2 (a + b - c) ≤ 3abc`.
-/
theorem candidate (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
    (h₁ : c < a + b) (h₂ : b < a + c) (h₃ : a < b + c) :
    a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c) ≤ 3 * a * b * c :=
