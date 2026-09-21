theorem candidate (f : ℝ → ℝ) :
    (∀ x y : ℝ, f (x - f y) = f (f y) + x * f y + f x - 1) ↔ (∀ x : ℝ, f x = 1 - x ^ 2 / 2) :=
